(* CARRIED from commit ae2fa80b0325f09472155bcfce1c36e649d6ff60,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfRoomStep.v, sha256 b627ac85e90f1503c6fd1cee4209b63725e41b92b2d371883cc11c0cfc7bd2d5 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by a Theorem Labs lane, 2026-10-30: rk_free_inner's restated tree takes free_cf's size test; its recycle side from rk_rchunk_fr; statement of rk_free unchanged. A change request to a Theorem Labs lane. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the ROOM STEPS over
   YGcfRoomKeep.v's ROOM_cf_k S k (STATE FIRST, then the headroom k).
   One malloc_cf adds at most one live secondary (none for a primary request), at most one class-full
   report (exh_len1 + exh_len2 c <= 100 bytes of error buffer, errb_size_cf being set, never remapped down),
   and at most one user map of class kBatchClass (its refill target is max_cached kBatchClass / 2 = 1 batch,
   so the map is at most kUserMapSize). One free_cf adds no secondary (sec_dealloc only removes), leaves the
   error buffer's size unchanged, and maps at most one more batch (enqueue). The realloc tree is free_cf PNull
   (a frame), malloc_cf, then free_cf on success: two units.
   Every bound holds on EVERY returning path of the model (YGcfAmx.v's ipost; ipost_apath turns it into a
   statement about apath), with no gflag: a refused ask maps nothing.
   The one state premise is room_shape_cf: class kBatchClass's region (alloc <= mapped, a non-negative free
   count) and cache (pc_max = max_cached once initialised), 32 regions and caches, and a non-negative
   error-buffer size. WfP_cf gives it (room_shape_cf_of_WfP_cf), so acall_pre_cf does; malloc_cf keeps it.
   No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG02 YG04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfPath YGcfAmx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YG0dcf ReallocP YGcfRealloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

Ltac rk_splits := repeat lazymatch goal with |- _ /\ _ => split end.
Ltac rk_if := match goal with |- context [if ?b then _ else _] => destruct b end; cbv beta iota.

(* ---------------------------------------------------------------------------- *)
(* 1. The error-buffer size as a list function.                                   *)
Fixpoint first_sz (l : list secmap) : Z :=
match l with [] => 0 | sm :: t => if is_errb_sz sm then sm_len sm else first_sz t end.

Lemma errb_size_first : forall s, errb_size_cf s = first_sz (st_secs s).
Proof.
intros s. unfold errb_size_cf.
assert (G : forall l pre, match find_sz l (length pre) with
  | Some i => match nth_error (pre ++ l) i with Some sm => sm_len sm | None => 0 end
  | None => 0 end = first_sz l).
{ induction l as [|sm t IH]; intros pre; cbn [find_sz first_sz]; [reflexivity|].
  destruct (is_errb_sz sm).
  - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - specialize (IH (pre ++ [sm])). rewrite length_app, <- app_assoc in IH. cbn [length app] in IH.
    rewrite Nat.add_1_r in IH. exact IH. }
exact (G (st_secs s) []).
Qed.

Lemma first_sz_nonneg : forall (m : Z) l, Forall (fun sm => 0 <= sm_len sm <= m) l -> 0 <= first_sz l.
Proof. intros m l H. induction H as [|sm t Hs Ht IH]; cbn [first_sz]; [lia|]. destruct (is_errb_sz sm); lia. Qed.

Lemma first_sz_app_nsz : forall l x, is_errb_sz x = false -> first_sz (l ++ [x]) = first_sz l.
Proof.
intros l x Hx. induction l as [|sm t IH]; cbn [app first_sz]; [rewrite Hx; reflexivity|].
destruct (is_errb_sz sm); [reflexivity | exact IH].
Qed.

Lemma first_sz_retire : forall l,
first_sz (map (fun sm => if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm) l) = first_sz l.
Proof.
induction l as [|sm t IH]; cbn [map first_sz]; [reflexivity|].
destruct (is_errb_cap sm) eqn:Ec.
- change (is_errb_sz (mkSec (sm_len sm) ERRB_DEAD_TAG false)) with false.
  replace (is_errb_sz sm) with false; [exact IH|].
  unfold is_errb_cap in Ec. unfold is_errb_sz. apply Z.eqb_eq in Ec. rewrite Ec. reflexivity.
- destruct (is_errb_sz sm); [reflexivity | exact IH].
Qed.

Lemma first_sz_set_found : forall x l j i, is_errb_sz x = true -> find_sz l j = Some i ->
(j <= i)%nat /\ first_sz (lupd l (i - j) x) = sm_len x.
Proof.
intros x l. induction l as [|sm t IH]; intros j i Hx H; cbn [find_sz] in H; [discriminate H|].
destruct (is_errb_sz sm) eqn:E.
- injection H as <-. rewrite Nat.sub_diag. cbn [lupd first_sz]. rewrite Hx. split; [lia | reflexivity].
- destruct (IH (S j) i Hx H) as [Hle Hf]. split; [lia|].
  replace (i - j)%nat with (S (i - S j)) by lia. cbn [lupd first_sz]. rewrite E. exact Hf.
Qed.

Lemma first_sz_app_none : forall x l j, find_sz l j = None -> first_sz (l ++ [x]) = if is_errb_sz x then sm_len x else 0.
Proof.
intros x l. induction l as [|sm t IH]; intros j H; cbn [find_sz app first_sz] in *; [reflexivity|].
destruct (is_errb_sz sm); [discriminate H | exact (IH (S j) H)].
Qed.

Lemma first_sz_lupd_same : forall l r sm x, nth_error l r = Some sm -> sm_size x = sm_size sm -> sm_len x = sm_len sm ->
first_sz (lupd l r x) = first_sz l.
Proof.
induction l as [|y t IH]; intros [|r] sm x H Hs Hl; cbn [nth_error lupd first_sz] in *; try discriminate H.
- injection H as ->. unfold is_errb_sz. rewrite Hs, Hl. reflexivity.
- destruct (is_errb_sz y); [reflexivity | exact (IH r sm x H Hs Hl)].
Qed.

Lemma errb_size_set : forall ns s, errb_size_cf (match find_sz (st_secs s) 0 with
| Some i => set_secs (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false)) s
| None => set_secs (st_secs s ++ [mkSec ns ERRB_SZ_TAG false]) s end) = ns.
Proof.
intros ns s. destruct (find_sz (st_secs s) 0) as [i|] eqn:E; rewrite errb_size_first; cbn [st_secs set_secs].
- destruct (first_sz_set_found (mkSec ns ERRB_SZ_TAG false) _ 0 i eq_refl E) as [_ H].
  rewrite Nat.sub_0_r in H. exact H.
- rewrite (first_sz_app_none _ _ 0 E). reflexivity.
Qed.

Lemma rk_ndigits : forall z, 1 <= ndigits z <= 5.
Proof. intros z. unfold ndigits. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.

Lemma rk_ndigits2 : forall z, z < 100 -> ndigits z <= 2.
Proof.
intros z Hz. unfold ndigits. destruct (Z.ltb_spec z 10); [lia|]. destruct (Z.ltb_spec z 100); lia.
Qed.

Lemma exh_len2_nonneg : forall c, 0 <= exh_len2 c.
Proof. intros c. unfold exh_len2. pose proof (rk_ndigits c). pose proof (rk_ndigits (class_size c)). lia. Qed.

(* One class-full report of a class below 100 costs at most 33 + 60 + 2 + 5 = 100 bytes. *)
Lemma exh_report_le_100 : forall c, c < 100 -> exh_len1 + exh_len2 c <= 100.
Proof.
intros c Hc. pose proof (rk_ndigits2 c Hc). pose proof (rk_ndigits (class_size c)).
unfold exh_len1, exh_len2. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. All-paths rules for the model's monad (ipost, YGcfAmx.v).                  *)
Lemma rk_bind {A B} (m : M B) (k : B -> M A) (s : astate) (P : A * astate -> Prop) :
ipost (m s) (fun r => ipost (k (fst r) (snd r)) P) -> ipost (bind m k s) P.
Proof. intros H. unfold bind. apply ipost_ibind. eapply ipost_mono; [|exact H]. intros [x s'] Hx. exact Hx. Qed.
Lemma rk_ret {A} (a : A) s (P : A * astate -> Prop) : P (a, s) -> ipost (ret a s) P.
Proof. intros H. exact H. Qed.
Lemma rk_get s (P : astate * astate -> Prop) : P (s, s) -> ipost (get s) P.
Proof. intros H. exact H. Qed.
Lemma rk_put s s' (P : unit * astate -> Prop) : P (tt, s') -> ipost (put s' s) P.
Proof. intros H. exact H. Qed.
Lemma rk_modify f s (P : unit * astate -> Prop) : P (tt, f s) -> ipost (modify f s) P.
Proof. intros H. exact H. Qed.
Lemma rk_tick s (P : unit * astate -> Prop) : P (tt, set_nev (st_nev s + 1) s) -> ipost (tick s) P.
Proof. intros H. exact H. Qed.
Lemma rk_get_region c s (P : region * astate -> Prop) : P (reg s c, s) -> ipost (get_region c s) P.
Proof. intros H. exact H. Qed.
Lemma rk_get_pc c s (P : pclass * astate -> Prop) : P (cache s c, s) -> ipost (get_pc c s) P.
Proof. intros H. exact H. Qed.
Lemma rk_set_region c r s (P : unit * astate -> Prop) :
P (tt, set_regions (zupd c r (st_regions s)) s) -> ipost (set_region c r s) P.
Proof. intros H. exact H. Qed.
Lemma rk_set_pc c p s (P : unit * astate -> Prop) :
P (tt, set_cache (zupd c p (st_cache s)) s) -> ipost (set_pc c p s) P.
Proof. intros H. exact H. Qed.
Lemma rk_mcheck (b : bool) tag s (P : unit * astate -> Prop) : (b = true -> P (tt, s)) -> ipost (mcheck b tag s) P.
Proof. intros H. destruct b; [exact (H eq_refl) | exact I]. Qed.
Lemma rk_askz q s (P : Z * astate -> Prop) : (forall z, P (z, s)) -> ipost (askz q s) P.
Proof. intros H. exact H. Qed.
Lemma rk_spin {A} pc s (P : A * astate -> Prop) : ipost (@spin A pc s) P.
Proof. exact I. Qed.
Lemma rk_fail {A} f s (P : A * astate -> Prop) : ipost (@fail A f s) P.
Proof. exact I. Qed.

(* A returning path satisfies every all-paths post. *)
Lemma ipost_apath : forall {A} (t : itree astate A) (P : A -> Prop) tr a, ipost t P -> apath t tr a -> P a.
Proof.
intros A t P. induction t as [a' | q sn k IH | pc | f]; intros tr a H Hp.
- destruct tr; cbn [apath] in Hp; [subst a'; exact H | destruct Hp].
- destruct tr as [|[q' z] tr']; cbn [apath] in Hp; [destruct Hp|]. destruct Hp as (_ & _ & Hp).
  exact (IH z tr' a (H z) Hp).
- destruct tr; cbn [apath] in Hp; destruct Hp.
- destruct tr; cbn [apath] in Hp; destruct Hp.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. List and free-array facts.                                                  *)
Lemma lupd_oob {X} : forall (l : list X) i v, (length l <= i)%nat -> lupd l i v = l.
Proof. induction l as [|h t IH]; intros [|i] v H; cbn [lupd length] in *; try reflexivity; try lia. f_equal. apply IH. lia. Qed.

Lemma rk_removelast_le {X} : forall (l : list X), (length (removelast l) <= length l)%nat.
Proof.
induction l as [|x t IH]; [cbn; lia|]. destruct t as [|y t'].
- cbn. lia.
- change (removelast (x :: y :: t')) with (x :: removelast (y :: t')). cbn [length] in *. lia.
Qed.

Lemma rk_fa_pop : forall sz l off l', fa_pop sz l = Some (off, l') -> fa_len l - 1 <= fa_len l'.
Proof.
intros sz l. induction l as [|f t IH]; intros off l'; cbn [fa_pop]; [intros H; discriminate H|].
destruct f as [lo k|o].
- destruct (Z.leb_spec k 0) as [Hk|Hk]; intros H; cbv beta iota in H.
  + specialize (IH off l' H). cbn [fa_len]. lia.
  + injection H as _ <-. destruct (Z.eqb_spec k 1); cbn [fa_len]; lia.
- intros H. injection H as _ <-. cbn [fa_len]. lia.
Qed.

Lemma rk_fa_pop_n : forall fuel sz n l acc tops rest, fa_pop_n fuel sz n l acc = Some (tops, rest) -> 0 <= n ->
fa_len l - n <= fa_len rest.
Proof.
induction fuel as [|f IH]; intros sz n l acc tops rest; cbn [fa_pop_n]; [intros H; discriminate H|].
destruct (Z.leb_spec n 0) as [Hle|Hgt]; intros H Hn; cbv beta iota in H.
- injection H as _ <-. lia.
- revert H. destruct (fa_pop sz l) as [[off l']|] eqn:Ep; intros H; cbv beta iota in H; [|discriminate H].
  pose proof (rk_fa_pop _ _ _ _ Ep) as P1. pose proof (IH _ _ _ _ _ _ H ltac:(lia)) as P2. lia.
Qed.

Lemma rk_reg_set_mapped : forall s c r x, rg_mapped_user r = rg_mapped_user (reg s c) ->
rg_mapped_user (reg (set_regions (zupd c r (st_regions s)) s) x) = rg_mapped_user (reg s x).
Proof.
intros s c r x H. unfold reg, znth, zupd in *. cbn [st_regions set_regions].
destruct (Nat.eq_dec (Z.to_nat c) (Z.to_nat x)) as [E|N].
- rewrite <- E. destruct (Nat.lt_ge_cases (Z.to_nat c) (length (st_regions s))) as [L|G].
  + rewrite nth_lupd_same by exact L. exact H.
  + rewrite lupd_oob by exact G. reflexivity.
- rewrite nth_lupd_other by exact N. reflexivity.
Qed.

Lemma rk_k24_lt : forall l : list region, length l = 32%nat -> (Z.to_nat kBatchClass < length l)%nat.
Proof. intros l H. rewrite H. apply Nat.ltb_lt. reflexivity. Qed.
Lemma rk_k24_ltc : forall l : list pclass, length l = 32%nat -> (Z.to_nat kBatchClass < length l)%nat.
Proof. intros l H. rewrite H. apply Nat.ltb_lt. reflexivity. Qed.

Lemma rk_needed_pos : forall n, from_primary n = false -> 0 < needed_size n.
Proof.
intros n Fp. unfold needed_size. rewrite Fp. unfold from_primary in Fp. apply Z.leb_gt in Fp.
pose proof (rz_size_pos n). unfold kMaxSize in Fp. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The state premise.                                                          *)
Section RS. Context {ci : CfImg} {cp : CfParams}.

Definition room_shape_cf (s : astate) : Prop :=
length (st_regions s) = 32%nat /\ length (st_cache s) = 32%nat /\
(st_cache_inited s = true -> pc_max (cache s kBatchClass) = max_cached kBatchClass) /\
rg_alloc_user (reg s kBatchClass) <= rg_mapped_user (reg s kBatchClass) /\
0 <= fa_len (rg_free (reg s kBatchClass)) /\
0 <= errb_size_cf s.

Lemma room_shape_cf_of_WfP_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> room_shape_cf s.
Proof.
intros U pp cc bb s W.
pose proof (wfc_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as C. unfold wf_class_cf in C.
split; [exact (wfc_len_regions _ _ _ _ _ W)|]. split; [exact (wfc_len_cache _ _ _ _ _ W)|].
split; [intros Hi; pose proof (wrc_cache _ _ _ _ _ _ C) as H; rewrite Hi in H; destruct H as [H _]; exact H|].
split; [exact (proj2 (wrc_alloc _ _ _ _ _ _ C))|].
split; [exact (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ C))|].
rewrite errb_size_first. apply (first_sz_nonneg cf_nob). exact (wsc_lens _ (wfc_secondary _ _ _ _ _ W)).
Qed.

Lemma room_shape_cf_init : room_shape_cf init_state.
Proof.
split; [reflexivity|]. split; [reflexivity|]. split; [intros H; discriminate H|].
rewrite reg_init. cbn [rg_alloc_user rg_mapped_user rg_free region0 fa_len].
split; [lia|]. split; [lia|]. assert (E : errb_size_cf init_state = 0) by reflexivity. lia.
Qed.

Lemma rk_inv_frame : forall s s', room_shape_cf s -> st_regions s' = st_regions s -> st_cache s' = st_cache s ->
st_cache_inited s' = st_cache_inited s -> errb_size_cf s' = errb_size_cf s -> room_shape_cf s'.
Proof. intros s s' IV R C In E. unfold room_shape_cf, reg, cache in *. rewrite R, C, In, E. exact IV. Qed.

(* The frame of the steps that touch no region, cache or secondary. *)
Definition rk_nt (s s' : astate) : Prop :=
st_regions s' = st_regions s /\ st_cache s' = st_cache s /\ st_cache_inited s' = st_cache_inited s /\
st_secs s' = st_secs s /\ st_sec_arr s' = st_sec_arr s.

Lemma rk_nt_refl : forall s, rk_nt s s.
Proof. intros s. unfold rk_nt. rk_splits; reflexivity. Qed.
Lemma rk_nt_trans : forall s1 s2 s3, rk_nt s1 s2 -> rk_nt s2 s3 -> rk_nt s1 s3.
Proof. intros s1 s2 s3 (A1 & B1 & C1 & D1 & E1) (A2 & B2 & C2 & D2 & E2). unfold rk_nt. rk_splits; congruence. Qed.
Lemma rk_nt_meas : forall s s', rk_nt s s' ->
reg s' kBatchClass = reg s kBatchClass /\ errb_size_cf s' = errb_size_cf s /\ st_sec_arr s' = st_sec_arr s.
Proof. intros s s' (A & B & C & D & E). unfold reg, errb_size_cf. rewrite A, D. rk_splits; [reflexivity | reflexivity | exact E]. Qed.
Lemma rk_nt_inv : forall s s', rk_nt s s' -> room_shape_cf s -> room_shape_cf s'.
Proof.
intros s s' (A & B & C & D & E) IV. apply (rk_inv_frame s s' IV A B C). unfold errb_size_cf. rewrite D. reflexivity.
Qed.

Lemma rk_depot : forall tr s, ipost (depot_put tr s) (fun r => rk_nt s (snd r)).
Proof.
intros tr s. unfold depot_put. apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply rk_nt_refl.
- apply rk_bind. apply rk_get. cbn [fst snd].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_put. cbn [snd]. unfold rk_nt. rk_splits; reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. The error buffer: a report adds at most exh_len1 + exh_len2 c bytes.         *)
Definition rk_nosec (s s' : astate) : Prop :=
st_regions s' = st_regions s /\ st_cache s' = st_cache s /\ st_cache_inited s' = st_cache_inited s /\
st_sec_arr s' = st_sec_arr s.

Lemma rk_nosec_trans : forall s1 s2 s3, rk_nosec s1 s2 -> rk_nosec s2 s3 -> rk_nosec s1 s3.
Proof. intros s1 s2 s3 (A1 & B1 & C1 & D1) (A2 & B2 & C2 & D2). unfold rk_nosec. rk_splits; congruence. Qed.

Lemma rk_errb_map : forall w s, ipost (errb_map_cf w s)
(fun r => rk_nosec s (snd r) /\ errb_size_cf (snd r) = errb_size_cf s).
Proof.
intros w s. unfold errb_map_cf. cbv zeta. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if; [apply rk_spin|].
apply rk_bind. unfold errb_retire. apply rk_modify. cbn [fst snd]. apply rk_modify. cbn [snd].
split; [unfold rk_nosec; cbn [st_regions st_cache st_cache_inited st_sec_arr set_secs set_nev]; rk_splits; reflexivity|].
rewrite !errb_size_first. cbn [st_secs set_secs set_nev].
rewrite first_sz_app_nsz by reflexivity. apply first_sz_retire.
Qed.

Lemma rk_errb_set : forall ns s, ipost (errb_set_size ns s) (fun r => rk_nosec s (snd r) /\ errb_size_cf (snd r) = ns).
Proof.
intros ns s. unfold errb_set_size. apply rk_modify. cbn [snd].
split; [|apply errb_size_set].
unfold rk_nosec. destruct (find_sz (st_secs s) 0); cbn [st_regions st_cache st_cache_inited st_sec_arr set_secs];
rk_splits; reflexivity.
Qed.

Lemma rk_errb_append : forall len s, 0 <= len -> ipost (errb_append_cf len s)
(fun r => rk_nosec s (snd r) /\ (0 <= errb_size_cf s -> 0 <= errb_size_cf (snd r) <= errb_size_cf s + len)).
Proof.
intros len s Hl. unfold errb_append_cf. cbv zeta. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (negb (errb_mapped_cf s)); cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply rk_errb_map]. intros [u s1] [F1 E1]. cbn [fst snd] in *.
  apply rk_bind. apply rk_get. cbn [fst snd].
  apply rk_bind. eapply ipost_mono with (P := fun r => rk_nosec s1 (snd r) /\ errb_size_cf (snd r) = errb_size_cf s1).
  2:{ destruct (errb_cap_cf s1 <? len); cbv beta iota;
      [apply rk_errb_map | apply rk_ret; cbn [snd]; split; [unfold rk_nosec; rk_splits; reflexivity | reflexivity]]. }
  intros [u2 s2] [F2 E2]. cbn [fst snd] in *.
  eapply ipost_mono; [|apply rk_errb_set]. intros [u3 s3] [F3 E3]. cbn [snd] in *.
  split; [eapply rk_nosec_trans; [exact F1 | eapply rk_nosec_trans; [exact F2 | exact F3]]|]. intros H0. lia.
- apply rk_bind. eapply ipost_mono with (P := fun r => rk_nosec s (snd r) /\ errb_size_cf (snd r) = errb_size_cf s).
  2:{ destruct (errb_cap_cf s <? errb_size_cf s + len); cbv beta iota;
      [apply rk_errb_map | apply rk_ret; cbn [snd]; split; [unfold rk_nosec; rk_splits; reflexivity | reflexivity]]. }
  intros [u2 s2] [F2 E2]. cbn [fst snd] in *.
  eapply ipost_mono; [|apply rk_errb_set]. intros [u3 s3] [F3 E3]. cbn [snd] in *.
  split; [eapply rk_nosec_trans; [exact F2 | exact F3]|]. intros H0. lia.
Qed.

Lemma rk_errb_report : forall c s, ipost (errb_report_cf c s)
(fun r => rk_nosec s (snd r) /\
(0 <= errb_size_cf s -> 0 <= errb_size_cf (snd r) <= errb_size_cf s + (exh_len1 + exh_len2 c))).
Proof.
intros c s. pose proof (exh_len2_nonneg c) as X. unfold errb_report_cf. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (exh_mem_cf s c); cbv beta iota.
- apply rk_ret. cbn [snd]. split; [unfold rk_nosec; rk_splits; reflexivity | unfold exh_len1; lia].
- apply rk_bind. eapply ipost_mono; [|apply rk_errb_append; unfold exh_len1; lia]. intros [u s1] [F1 E1]. cbn [fst snd] in *.
  eapply ipost_mono; [|apply rk_errb_append; exact X]. intros [u2 s2] [F2 E2]. cbn [snd] in *.
  split; [eapply rk_nosec_trans; [exact F1 | exact F2]|]. intros H0. unfold exh_len1 in *.
  specialize (E1 H0). specialize (E2 ltac:(lia)). lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. ensure_free_array on a class in range: the class's three counts are kept.   *)
Definition rk_efa (c : Z) (s s' : astate) : Prop :=
length (st_regions s') = length (st_regions s) /\ (forall x, 0 <= x -> x <> c -> reg s' x = reg s x) /\
rg_mapped_user (reg s' c) = rg_mapped_user (reg s c) /\ rg_alloc_user (reg s' c) = rg_alloc_user (reg s c) /\
rg_free (reg s' c) = rg_free (reg s c) /\
st_cache s' = st_cache s /\ st_cache_inited s' = st_cache_inited s /\ st_secs s' = st_secs s /\ st_sec_arr s' = st_sec_arr s.

Lemma rk_efa_refl : forall c s, rk_efa c s s.
Proof. intros c s. unfold rk_efa. rk_splits; try reflexivity; intros x _ _; reflexivity. Qed.

Lemma rk_efa_set : forall c s r, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
rg_mapped_user r = rg_mapped_user (reg s c) -> rg_alloc_user r = rg_alloc_user (reg s c) -> rg_free r = rg_free (reg s c) ->
rk_efa c s (set_regions (zupd c r (st_regions s)) s).
Proof.
intros c s r Hc Hl E1 E2 E3. unfold rk_efa. rewrite !(reg_upd_same s c r Hc Hl).
split; [exact (zupd_length c r (st_regions s))|]. split; [intros x Hx Hne; apply reg_upd_other; lia|].
split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. rk_splits; reflexivity.
Qed.

Lemma rk_efa_path : forall c need sof s, 0 <= c -> (Z.to_nat c < length (st_regions s))%nat ->
ipost (ensure_free_array c need sof s) (fun r => rk_efa c s (snd r)).
Proof.
intros c need sof s Hc Hl. unfold ensure_free_array. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply rk_efa_refl.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
    apply rk_efa_set; try assumption; reflexivity.
  + apply rk_bind. eapply ipost_mono with (P := fun r => rk_efa c s (snd r)).
    2:{ destruct (aDestroyed z); cbv beta iota.
        - apply rk_set_region. cbn [snd]. apply rk_efa_set; try assumption; reflexivity.
        - apply rk_ret. cbn [snd]. apply rk_efa_refl. }
    intros [u s1] H1. cbn [fst snd] in *. destruct sof; cbv beta iota; [apply rk_spin | apply rk_ret; exact H1].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 7. A class c other than kBatchClass: class kBatchClass's region and cache are  *)
(*    untouched, and the error buffer grows by at most one report.               *)
Definition rk_cfr (E : Z) (s s' : astate) : Prop :=
length (st_regions s') = length (st_regions s) /\ reg s' kBatchClass = reg s kBatchClass /\
length (st_cache s') = length (st_cache s) /\ cache s' kBatchClass = cache s kBatchClass /\
st_cache_inited s' = st_cache_inited s /\ st_sec_arr s' = st_sec_arr s /\
(0 <= errb_size_cf s -> 0 <= errb_size_cf s' <= errb_size_cf s + E).

Lemma rk_cfr_refl : forall s, rk_cfr 0 s s.
Proof. intros s. unfold rk_cfr. rk_splits; try reflexivity. intros H; lia. Qed.
Lemma rk_cfr_trans : forall E1 E2 s1 s2 s3, rk_cfr E1 s1 s2 -> rk_cfr E2 s2 s3 -> rk_cfr (E1 + E2) s1 s3.
Proof.
intros E1 E2 s1 s2 s3 (A1 & B1 & C1 & D1 & F1 & G1 & H1) (A2 & B2 & C2 & D2 & F2 & G2 & H2).
unfold rk_cfr. rk_splits; try congruence. intros H0. specialize (H1 H0). specialize (H2 (proj1 H1)). lia.
Qed.
Lemma rk_cfr_mono : forall E1 E2 s s', E1 <= E2 -> rk_cfr E1 s s' -> rk_cfr E2 s s'.
Proof. intros E1 E2 s s' HE (A & B & C & D & F & G & H). unfold rk_cfr. rk_splits; try assumption. intros H0. specialize (H H0). lia. Qed.
Lemma rk_cfr_inv : forall E s s', room_shape_cf s -> rk_cfr E s s' -> room_shape_cf s'.
Proof.
intros E s s' (Lr & Lc & P & A & F & Eb) (A1 & B1 & C1 & D1 & F1 & G1 & H1). unfold room_shape_cf.
rewrite A1, B1, C1, D1, F1. rk_splits; try assumption. exact (proj1 (H1 Eb)).
Qed.
Lemma rk_cfr_set_region : forall c r s, 0 <= c -> c <> kBatchClass -> rk_cfr 0 s (set_regions (zupd c r (st_regions s)) s).
Proof.
intros c r s Hc Hn. unfold rk_cfr.
rewrite (reg_upd_other s c kBatchClass r Hc ltac:(unfold kBatchClass; lia) Hn).
split; [exact (zupd_length c r (st_regions s))|].
rk_splits; try reflexivity. intros H. change (errb_size_cf (set_regions (zupd c r (st_regions s)) s)) with (errb_size_cf s). lia.
Qed.
Lemma rk_cfr_set_pc : forall c p s, 0 <= c -> c <> kBatchClass -> rk_cfr 0 s (set_cache (zupd c p (st_cache s)) s).
Proof.
intros c p s Hc Hn. unfold rk_cfr.
rewrite (cache_upd_other s c kBatchClass p Hc ltac:(unfold kBatchClass; lia) Hn).
split; [reflexivity|]. split; [reflexivity|]. split; [exact (zupd_length c p (st_cache s))|].
rk_splits; try reflexivity. intros H. change (errb_size_cf (set_cache (zupd c p (st_cache s)) s)) with (errb_size_cf s). lia.
Qed.
Lemma rk_cfr_of_efa : forall c s s', c <> kBatchClass -> rk_efa c s s' -> rk_cfr 0 s s'.
Proof.
intros c s s' Hn (L & O & _ & _ & _ & C & In & Se & Sa). unfold rk_cfr.
rewrite (O kBatchClass ltac:(unfold kBatchClass; lia) (fun E => Hn (eq_sym E))).
unfold cache, errb_size_cf. rewrite L, C, In, Se, Sa. rk_splits; try reflexivity. intros H; lia.
Qed.
Lemma rk_cfr_of_nosec : forall E s s', rk_nosec s s' ->
(0 <= errb_size_cf s -> 0 <= errb_size_cf s' <= errb_size_cf s + E) -> rk_cfr E s s'.
Proof. intros E s s' (A & B & C & D) H. unfold rk_cfr, reg, cache. rewrite A, B, C, D. rk_splits; try reflexivity. exact H. Qed.

Lemma rk_set_exh : forall c s, 0 <= c -> c <> kBatchClass -> ipost (set_exh_cf c s) (fun r => rk_cfr 0 s (snd r)).
Proof.
intros c s Hc Hn. unfold set_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_set_region. cbn [snd]. apply rk_cfr_set_region; assumption.
Qed.
Lemma rk_clear_exh : forall c s, 0 <= c -> c <> kBatchClass -> ipost (clear_exh_cf c s) (fun r => rk_cfr 0 s (snd r)).
Proof.
intros c s Hc Hn. unfold clear_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_set_region. cbn [snd]. apply rk_cfr_set_region; assumption.
Qed.

Lemma rk_mmu_cf : forall c need s, 0 <= c -> c <> kBatchClass ->
ipost (map_more_user_cf c need s) (fun r => rk_cfr (exh_len1 + exh_len2 c) s (snd r)).
Proof.
intros c need s Hc Hn. pose proof (exh_len2_nonneg c) as X. assert (HE : 0 <= exh_len1 + exh_len2 c) by (unfold exh_len1; lia).
unfold map_more_user_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|]. cbv beta iota zeta.
apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- rk_if.
  + apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. destruct (aGranted z); cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
      eapply rk_cfr_mono; [exact HE | apply rk_cfr_set_region; assumption].
    * apply rk_bind. eapply ipost_mono with (P := fun r => rk_cfr 0 s (snd r)).
      2:{ destruct (aDestroyed z); cbv beta iota;
          [apply rk_set_region; cbn [snd]; apply rk_cfr_set_region; assumption | apply rk_ret; cbn [snd]; apply rk_cfr_refl]. }
      intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. cbn [snd]. eapply rk_cfr_mono; [exact HE | exact H1].
  + apply rk_bind. eapply ipost_mono; [|apply rk_errb_report]. intros [u s1] [N1 E1]. cbn [fst snd] in *.
    pose proof (rk_cfr_of_nosec _ _ _ N1 E1) as C1.
    apply rk_bind. eapply ipost_mono; [|apply rk_set_exh; assumption]. intros [u2 s2] C2. cbn [fst snd] in *.
    apply rk_ret. cbn [snd]. eapply rk_cfr_mono; [|exact (rk_cfr_trans _ _ _ _ _ C1 C2)]. lia.
- apply rk_ret. cbn [snd]. eapply rk_cfr_mono; [exact HE | apply rk_cfr_refl].
Qed.

Lemma rk_populate_cf : forall c need s, 0 <= c -> c <> kBatchClass -> (Z.to_nat c < length (st_regions s))%nat ->
ipost (populate_cf c need s) (fun r => rk_cfr (exh_len1 + exh_len2 c) s (snd r)).
Proof.
intros c need s Hc Hn Hl.
unfold populate_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|]. cbv beta iota zeta.
apply rk_bind. eapply ipost_mono; [|apply rk_mmu_cf; assumption]. intros [ok s1] C1. cbn [fst snd] in *.
pose proof C1 as (L1 & _).
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd].
  apply rk_bind. eapply ipost_mono; [|apply rk_efa_path; [exact Hc | rewrite L1; exact Hl]]. intros [ok2 s2] E2. cbn [fst snd] in *.
  pose proof (rk_cfr_of_efa _ _ _ Hn E2) as C2.
  destruct ok2; cbn [negb]; cbv beta iota.
  + apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
    apply rk_bind. eapply ipost_mono; [|apply rk_clear_exh; assumption]. intros [u4 s4] C4. cbn [fst snd] in *.
    apply rk_ret. cbn [snd].
    eapply rk_cfr_mono; [|exact (rk_cfr_trans _ _ _ _ _ (rk_cfr_trans _ _ _ _ _ (rk_cfr_trans _ _ _ _ _ C1 C2)
      (rk_cfr_set_region c _ s2 Hc Hn)) C4)]. lia.
  + apply rk_ret. cbn [snd]. eapply rk_cfr_mono; [|exact (rk_cfr_trans _ _ _ _ _ C1 C2)]. lia.
- apply rk_ret. cbn [snd]. exact C1.
Qed.

Lemma rk_gfa_cf : forall c n s, 0 <= c -> c <> kBatchClass -> (Z.to_nat c < length (st_regions s))%nat ->
ipost (get_from_allocator_cf c n s) (fun r => rk_cfr (exh_len1 + exh_len2 c) s (snd r)).
Proof.
intros c n s Hc Hn Hl. pose proof (exh_len2_nonneg c) as X. assert (HE : 0 <= exh_len1 + exh_len2 c) by (unfold exh_len1; lia).
unfold get_from_allocator_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_cfr (exh_len1 + exh_len2 c) s (snd r)).
2:{ rk_if; [apply rk_populate_cf; assumption | apply rk_ret; cbn [snd]; eapply rk_cfr_mono; [exact HE | apply rk_cfr_refl]]. }
intros [ok s1] C1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd]. rk_if.
  + apply rk_ret. cbn [snd]. exact C1.
  + match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
    cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
      eapply rk_cfr_mono; [|exact (rk_cfr_trans _ _ _ _ _ C1 (rk_cfr_set_region c _ s1 Hc Hn))]. lia.
    * apply rk_fail.
- apply rk_ret. cbn [snd]. exact C1.
Qed.

Lemma rk_refill_cf : forall c s, 0 <= c -> c <> kBatchClass -> (Z.to_nat c < length (st_regions s))%nat ->
ipost (refill_if_empty_cf c s) (fun r => rk_cfr (exh_len1 + exh_len2 c) s (snd r)).
Proof.
intros c s Hc Hn Hl. pose proof (exh_len2_nonneg c) as X. assert (HE : 0 <= exh_len1 + exh_len2 c) by (unfold exh_len1; lia).
unfold refill_if_empty_cf. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s c)) as [|x l]; cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply rk_gfa_cf; assumption]. intros [got s1] C1. cbn [fst snd] in *.
  destruct got as [tops|]; cbv beta iota.
  + apply rk_set_pc. cbn [snd]. eapply rk_cfr_mono; [|exact (rk_cfr_trans _ _ _ _ _ C1 (rk_cfr_set_pc c _ s1 Hc Hn))]. lia.
  + apply rk_ret. cbn [snd]. exact C1.
- apply rk_ret. cbn [snd]. eapply rk_cfr_mono; [exact HE | apply rk_cfr_refl].
Qed.

Lemma rk_init : forall s, room_shape_cf s -> ipost (init_cache_if_needed s) (fun r => room_shape_cf (snd r) /\
st_regions (snd r) = st_regions s /\ st_secs (snd r) = st_secs s /\ st_sec_arr (snd r) = st_sec_arr s /\
st_cache_inited (snd r) = true /\ pc_max (cache (snd r) kBatchClass) = max_cached kBatchClass).
Proof.
intros s IV. pose proof IV as (Lr & Lc & P & A & F & E). unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (st_cache_inited s) eqn:Ei; cbv beta iota.
- apply rk_ret. cbn [snd]. rk_splits; try reflexivity; auto.
- apply rk_put. cbn [snd].
  assert (CA : cache (set_cache_inited true (set_cache (init_caches (st_cache s)) s)) kBatchClass =
    mkPC (max_cached kBatchClass) (pc_chunks (cache s kBatchClass))) by (apply cache_after_init; unfold kBatchClass; lia).
  assert (LC : length (st_cache (set_cache_inited true (set_cache (init_caches (st_cache s)) s))) = 32%nat)
    by exact (length_init_caches (st_cache s)).
  unfold room_shape_cf. rewrite CA. cbn [pc_max].
  rk_splits; try assumption; try reflexivity; intros _; reflexivity.
Qed.

Lemma rk_cache_alloc_cf_other : forall c s, 1 <= c <= 31 -> c <> kBatchClass -> room_shape_cf s ->
ipost (cache_alloc_cf c s) (fun r => room_shape_cf (snd r) /\ st_sec_arr (snd r) = st_sec_arr s /\
errb_size_cf (snd r) <= errb_size_cf s + (exh_len1 + exh_len2 c) /\
rg_mapped_user (reg (snd r) kBatchClass) = rg_mapped_user (reg s kBatchClass)).
Proof.
intros c s Hc Hn IV. unfold cache_alloc_cf. apply rk_bind. eapply ipost_mono; [|apply rk_init; exact IV].
intros [u s1] (I1 & R1 & S1 & A1 & _ & _). cbn [fst snd] in *.
assert (Eb1 : errb_size_cf s1 = errb_size_cf s) by (unfold errb_size_cf; rewrite S1; reflexivity).
assert (Rg1 : reg s1 kBatchClass = reg s kBatchClass) by (unfold reg; rewrite R1; reflexivity).
pose proof I1 as (Lr1 & _ & _ & _ & _ & E1).
assert (Hl1 : (Z.to_nat c < length (st_regions s1))%nat) by (rewrite Lr1; lia).
apply rk_bind. eapply ipost_mono; [|apply rk_refill_cf; [lia | exact Hn | exact Hl1]]. intros [u2 s2] C2. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|x l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. pose proof C2 as (_ & B2 & _ & _ & _ & G2 & H2).
  split; [exact (rk_cfr_inv _ _ _ I1 C2)|]. split; [congruence|]. split; [specialize (H2 E1); lia | congruence].
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd].
  match goal with |- context [set_cache (zupd c ?p (st_cache s2)) s2] =>
    pose proof (rk_cfr_trans _ _ _ _ _ C2 (rk_cfr_set_pc c p s2 ltac:(lia) Hn)) as C3 end.
  pose proof C3 as (_ & B3 & _ & _ & _ & G3 & H3).
  split; [exact (rk_cfr_inv _ _ _ I1 C3)|]. split; [congruence|]. split; [specialize (H3 E1); lia | congruence].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 8. Class kBatchClass (cgif's own functions): at most one user map, of at most   *)
(*    kUserMapSize, since its refill target is max_cached kBatchClass / 2 = 1.     *)
Definition rk_c24 (D : Z) (s s' : astate) : Prop :=
length (st_regions s') = length (st_regions s) /\ st_cache s' = st_cache s /\ st_cache_inited s' = st_cache_inited s /\
st_secs s' = st_secs s /\ st_sec_arr s' = st_sec_arr s /\
rg_alloc_user (reg s' kBatchClass) <= rg_mapped_user (reg s' kBatchClass) /\ 0 <= fa_len (rg_free (reg s' kBatchClass)) /\
rg_mapped_user (reg s' kBatchClass) <= rg_mapped_user (reg s kBatchClass) + D.

Lemma rk_c24_refl : forall D s, 0 <= D -> rg_alloc_user (reg s kBatchClass) <= rg_mapped_user (reg s kBatchClass) ->
0 <= fa_len (rg_free (reg s kBatchClass)) -> rk_c24 D s s.
Proof. intros D s HD H1 H2. unfold rk_c24. rk_splits; try reflexivity; lia. Qed.
Lemma rk_c24_trans : forall D1 D2 s1 s2 s3, rk_c24 D1 s1 s2 -> rk_c24 D2 s2 s3 -> rk_c24 (D1 + D2) s1 s3.
Proof.
intros D1 D2 s1 s2 s3 (A1 & B1 & C1 & E1 & F1 & G1 & H1 & I1) (A2 & B2 & C2 & E2 & F2 & G2 & H2 & I2).
unfold rk_c24. rk_splits; try congruence; lia.
Qed.
Lemma rk_c24_mono : forall D1 D2 s s', D1 <= D2 -> rk_c24 D1 s s' -> rk_c24 D2 s s'.
Proof. intros D1 D2 s s' HD (A & B & C & E & F & G & H & I0). unfold rk_c24. rk_splits; try assumption; lia. Qed.
Lemma rk_c24_set : forall D s r, length (st_regions s) = 32%nat ->
rg_alloc_user r <= rg_mapped_user r -> 0 <= fa_len (rg_free r) -> rg_mapped_user r <= rg_mapped_user (reg s kBatchClass) + D ->
rk_c24 D s (set_regions (zupd kBatchClass r (st_regions s)) s).
Proof.
intros D s r Hl H1 H2 H3. unfold rk_c24.
rewrite !(reg_upd_same s kBatchClass r ltac:(unfold kBatchClass; lia) (rk_k24_lt _ Hl)).
split; [exact (zupd_length kBatchClass r (st_regions s))|].
rk_splits; try reflexivity; assumption.
Qed.
Lemma rk_c24_of_efa : forall s s', rg_alloc_user (reg s kBatchClass) <= rg_mapped_user (reg s kBatchClass) ->
0 <= fa_len (rg_free (reg s kBatchClass)) -> rk_efa kBatchClass s s' -> rk_c24 0 s s'.
Proof.
intros s s' H1 H2 (A & _ & M & Al & F & C & In & Se & Sa). unfold rk_c24. rewrite M, Al, F.
rk_splits; try assumption; lia.
Qed.
Lemma rk_inv_of_c24 : forall D s s', room_shape_cf s -> rk_c24 D s s' -> room_shape_cf s'.
Proof.
intros D s s' (Lr & Lc & P & A & F & E) (L & C & In & Se & Sa & A' & F' & M).
unfold room_shape_cf, cache, errb_size_cf in *. rewrite L, C, In, Se. rk_splits; assumption.
Qed.

Lemma rk_mmu24 : forall need s, length (st_regions s) = 32%nat ->
rg_alloc_user (reg s kBatchClass) <= rg_mapped_user (reg s kBatchClass) -> 0 <= fa_len (rg_free (reg s kBatchClass)) ->
need <= 1 -> ipost (map_more_user kBatchClass need s) (fun r => rk_c24 kUserMapSize s (snd r)).
Proof.
intros need s Hl H1 H2 Hn. assert (Hsz : class_size kBatchClass = 8192) by reflexivity.
assert (HK : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold map_more_user. cbv zeta. rewrite Hsz. apply rk_bind. apply rk_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg s kBatchClass)) (rg_alloc_user (reg s kBatchClass) + need * 8192)) as [Hlt|Hge];
cbv beta iota.
- assert (HX : rg_alloc_user (reg s kBatchClass) + need * 8192 - rg_mapped_user (reg s kBatchClass) <= kUserMapSize)
    by (unfold kUserMapSize; lia).
  pose proof (round_up_le _ kUserMapSize kUserMapSize ltac:(unfold kUserMapSize; lia) HX ltac:(reflexivity)) as RU.
  pose proof (round_up_ge (rg_alloc_user (reg s kBatchClass) + need * 8192 - rg_mapped_user (reg s kBatchClass))
    kUserMapSize ltac:(unfold kUserMapSize; lia)) as [[RG _] _].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
    apply rk_c24_set; cbn [rg_alloc_user rg_mapped_user rg_free]; [exact Hl | lia | exact H2 | lia].
  + apply rk_bind. eapply ipost_mono with (P := fun r => rk_c24 0 s (snd r)).
    2:{ destruct (aDestroyed z); cbv beta iota.
        - apply rk_set_region. cbn [snd].
          apply rk_c24_set; cbn [rg_alloc_user rg_mapped_user rg_free]; [exact Hl | lia | exact H2 | lia].
        - apply rk_ret. cbn [snd]. apply rk_c24_refl; [lia | exact H1 | exact H2]. }
    intros [u s1] Hs1. cbn [fst snd] in *. apply rk_ret. cbn [snd]. eapply rk_c24_mono; [|exact Hs1]. exact HK.
- apply rk_ret. cbn [snd]. apply rk_c24_refl; [exact HK | exact H1 | exact H2].
Qed.

Lemma rk_populate24 : forall need s, length (st_regions s) = 32%nat ->
rg_alloc_user (reg s kBatchClass) <= rg_mapped_user (reg s kBatchClass) -> 0 <= fa_len (rg_free (reg s kBatchClass)) ->
need <= 1 -> ipost (populate kBatchClass need s) (fun r => rk_c24 kUserMapSize s (snd r)).
Proof.
intros need s Hl H1 H2 Hn. assert (Hsz : class_size kBatchClass = 8192) by reflexivity.
assert (HK : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold populate. cbv zeta. rewrite Hsz.
apply rk_bind. eapply ipost_mono; [|apply rk_mmu24; assumption]. intros [ok s1] C1. cbn [fst snd] in *.
pose proof C1 as (L1 & _ & _ & _ & _ & A1 & F1 & _). rewrite Hl in L1.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd].
  apply rk_bind. eapply ipost_mono; [|apply rk_efa_path; [unfold kBatchClass; lia | exact (rk_k24_lt _ L1)]].
  intros [ok2 s2] E2. cbn [fst snd] in *. pose proof E2 as (L2 & _ & M2 & Al2 & Fr2 & _). rewrite L1 in L2.
  pose proof (rk_c24_of_efa s1 s2 A1 F1 E2) as C2.
  destruct ok2; cbn [negb]; cbv beta iota.
  + apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
    apply rk_ret. cbn [snd].
    apply (rk_c24_mono (kUserMapSize + 0 + 0)); [lia|].
    eapply rk_c24_trans; [exact (rk_c24_trans _ _ _ _ _ C1 C2)|].
    apply rk_c24_set; [exact L2 | | | ]; cbn [rg_alloc_user rg_mapped_user rg_free fa_len]; rewrite ?M2, ?Al2, ?Fr2.
    * pose proof (Z.mul_div_le (rg_mapped_user (reg s1 kBatchClass) - rg_alloc_user (reg s1 kBatchClass)) 8192 ltac:(lia)). lia.
    * pose proof (Z.div_pos (rg_mapped_user (reg s1 kBatchClass) - rg_alloc_user (reg s1 kBatchClass)) 8192 ltac:(lia) ltac:(lia)). lia.
    * lia.
  + apply rk_ret. cbn [snd]. apply (rk_c24_mono (kUserMapSize + 0)); [lia|]. exact (rk_c24_trans _ _ _ _ _ C1 C2).
- apply rk_ret. cbn [snd]. exact C1.
Qed.

Lemma rk_gfa24 : forall n s, length (st_regions s) = 32%nat ->
rg_alloc_user (reg s kBatchClass) <= rg_mapped_user (reg s kBatchClass) -> 0 <= fa_len (rg_free (reg s kBatchClass)) ->
0 <= n <= 1 -> ipost (get_from_allocator kBatchClass n s) (fun r => rk_c24 kUserMapSize s (snd r)).
Proof.
intros n s Hl H1 H2 Hn. assert (HK : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold get_from_allocator. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_c24 kUserMapSize s (snd r)).
2:{ destruct (Z.ltb_spec (fa_len (rg_free (reg s kBatchClass))) n); cbv beta iota.
    - apply rk_populate24; [exact Hl | exact H1 | exact H2 | lia].
    - apply rk_ret. cbn [snd]. apply rk_c24_refl; [exact HK | exact H1 | exact H2]. }
intros [ok s1] C1. cbn [fst snd] in *. pose proof C1 as (L1 & _ & _ & _ & _ & A1 & F1 & _). rewrite Hl in L1.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd].
  destruct (Z.ltb_spec (fa_len (rg_free (reg s1 kBatchClass))) n) as [Hlt|Hge]; cbv beta iota.
  + apply rk_ret. cbn [snd]. exact C1.
  + match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] eqn:Ep end;
    cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
      pose proof (rk_fa_pop_n _ _ _ _ _ _ _ Ep ltac:(lia)) as FP.
      apply (rk_c24_mono (kUserMapSize + 0)); [lia|]. eapply rk_c24_trans; [exact C1|].
      apply rk_c24_set; cbn [rg_alloc_user rg_mapped_user rg_free]; [exact L1 | exact A1 | lia | lia].
    * apply rk_fail.
- apply rk_ret. cbn [snd]. exact C1.
Qed.

Lemma rk_inv_set_pc24 : forall s l, room_shape_cf s -> st_cache_inited s = true ->
room_shape_cf (set_cache (zupd kBatchClass (mkPC (pc_max (cache s kBatchClass)) l) (st_cache s)) s).
Proof.
intros s l IV Hi. pose proof IV as (Lr & Lc & P & A & F & E). unfold room_shape_cf.
rewrite cache_upd_same by (first [unfold kBatchClass; lia | exact (rk_k24_ltc _ Lc)]).
cbn [st_regions st_cache st_cache_inited pc_max set_cache]. rewrite zupd_length.
rk_splits; try assumption; intros _; exact (P Hi).
Qed.

Lemma rk_cache_alloc24 : forall s, room_shape_cf s -> ipost (cache_alloc kBatchClass s) (fun r => room_shape_cf (snd r) /\
st_secs (snd r) = st_secs s /\ st_sec_arr (snd r) = st_sec_arr s /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize).
Proof.
intros s IV. assert (KU : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
assert (Er : forall v t, reg (set_cache v t) kBatchClass = reg t kBatchClass) by reflexivity.
unfold cache_alloc. apply rk_bind. eapply ipost_mono; [|apply rk_init; exact IV].
intros [u s1] (I1 & R1 & S1 & A1 & In1 & P1). cbn [fst snd] in *.
assert (M1 : reg s1 kBatchClass = reg s kBatchClass) by (unfold reg; rewrite R1; reflexivity).
pose proof I1 as (Lr1 & Lc1 & _ & Al1 & F1 & _).
apply rk_bind. eapply ipost_mono with (P := fun r => room_shape_cf (snd r) /\ st_secs (snd r) = st_secs s1 /\
  st_sec_arr (snd r) = st_sec_arr s1 /\
  rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s1 kBatchClass) + kUserMapSize /\
  st_cache_inited (snd r) = true).
2:{ unfold refill_if_empty. apply rk_bind. apply rk_get_pc. cbn [fst snd].
    destruct (pc_chunks (cache s1 kBatchClass)) as [|x l]; cbv beta iota.
    - apply rk_bind. eapply ipost_mono; [|apply rk_gfa24; [exact Lr1 | exact Al1 | exact F1 |
        rewrite P1; change (max_cached kBatchClass / 2) with 1; lia]].
      intros [got s2] C2. cbn [fst snd] in *.
      pose proof (rk_inv_of_c24 _ _ _ I1 C2) as I2.
      pose proof C2 as (_ & Ca2 & In2 & S2 & Sa2 & _ & _ & M2).
      assert (In2' : st_cache_inited s2 = true) by congruence.
      destruct got as [tops|]; cbv beta iota.
      + apply rk_set_pc. cbn [snd].
        replace (cache s1 kBatchClass) with (cache s2 kBatchClass) by (unfold cache; rewrite Ca2; reflexivity).
        split; [exact (rk_inv_set_pc24 s2 _ I2 In2')|]. rewrite Er.
        cbn [st_secs st_sec_arr st_cache_inited set_cache]. rk_splits; assumption.
      + apply rk_ret. cbn [snd]. rk_splits; assumption.
    - apply rk_ret. cbn [snd]. rk_splits; try assumption; try reflexivity; lia. }
intros [u2 s2] (I2 & S2 & A2 & M2 & In2). cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 kBatchClass)) as [|x l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. rewrite <- M1. rk_splits; [exact I2 | congruence | congruence | exact M2].
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd].
  rewrite Er, <- M1. cbn [st_secs st_sec_arr set_cache].
  rk_splits; [exact (rk_inv_set_pc24 s2 _ I2 In2) | congruence | congruence | exact M2].
Qed.

(* malloc_cf on class kBatchClass is cgif's text: populate_cf kBatchClass is populate kBatchClass. *)
Lemma cache_alloc_cf_24 : forall s, cache_alloc_cf kBatchClass s = cache_alloc kBatchClass s.
Proof.
intros s. unfold cache_alloc_cf, cache_alloc, refill_if_empty_cf, refill_if_empty, get_from_allocator_cf,
get_from_allocator, populate_cf. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 9. sec_alloc: one more entry in st_sec_arr, and the error buffer's size kept.  *)
Lemma rk_sec_alloc : forall n s, from_primary n = false -> ipost (sec_alloc n s) (fun r =>
st_regions (snd r) = st_regions s /\ st_cache (snd r) = st_cache s /\ st_cache_inited (snd r) = st_cache_inited s /\
errb_size_cf (snd r) = errb_size_cf s /\ (length (st_sec_arr (snd r)) <= S (length (st_sec_arr s)))%nat).
Proof.
intros n s Fp. pose proof (rk_needed_pos n Fp) as Np. unfold sec_alloc. cbv zeta.
apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. rk_splits; try reflexivity; lia.
- apply rk_bind. apply rk_get. cbn [fst snd].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_put. cbn [fst snd].
  apply rk_bind. eapply ipost_mono with (P := fun r => st_regions (snd r) = st_regions s /\ st_cache (snd r) = st_cache s /\
    st_cache_inited (snd r) = st_cache_inited s /\
    st_secs (snd r) = st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true] /\
    st_sec_arr (snd r) = st_sec_arr s).
  2:{ rk_if.
      - apply rk_bind. apply rk_askz. intros z2. cbn [fst snd]. rk_if.
        + apply rk_modify. cbn [snd]. rk_splits; reflexivity.
        + apply rk_spin.
      - apply rk_ret. cbn [snd]. rk_splits; reflexivity. }
  intros [u s3] (R3 & C3 & I3 & S3 & A3). cbn [fst snd] in *.
  apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret. cbn [snd].
  rk_splits; try assumption.
  + rewrite !errb_size_first. cbn [st_secs set_sec_arr]. rewrite S3. apply first_sz_app_nsz.
    unfold is_errb_sz. cbn [sm_size]. apply Z.eqb_neq. unfold ERRB_SZ_TAG. lia.
  + cbn [st_sec_arr set_sec_arr]. rewrite A3, length_app. cbn [length]. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 10. malloc_cf.                                                                  *)
Definition rk_mpost (a : Z) (s s' : astate) : Prop :=
room_shape_cf s' /\ Z.of_nat (length (st_sec_arr s')) <= Z.of_nat (length (st_sec_arr s)) + a /\
errb_size_cf s' <= errb_size_cf s + 100 /\
rg_mapped_user (reg s' kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize.

Lemma rk_mpost_nt_r : forall a s s1 s2, rk_mpost a s s1 -> rk_nt s1 s2 -> rk_mpost a s s2.
Proof.
intros a s s1 s2 (IV & L & E & M) N. pose proof (rk_nt_meas _ _ N) as (R & Eb & Sa).
split; [exact (rk_nt_inv _ _ N IV)|]. rewrite R, Eb, Sa. split; [exact L|]. split; [exact E | exact M].
Qed.

Theorem rk_malloc : forall n tr s, room_shape_cf s ->
ipost (malloc_cf n tr s) (fun r => rk_mpost (if from_primary n then 0 else 1) s (snd r)).
Proof.
intros n tr s IV. assert (KU : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold malloc_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
set (s0 := set_nev (st_nev s + 1) s).
assert (N0 : rk_nt s s0) by (unfold rk_nt; rk_splits; reflexivity).
assert (I0 : room_shape_cf s0) by exact (rk_nt_inv _ _ N0 IV).
assert (E0 : errb_size_cf s0 = errb_size_cf s) by reflexivity.
assert (A0 : st_sec_arr s0 = st_sec_arr s) by reflexivity.
assert (R0 : reg s0 kBatchClass = reg s kBatchClass) by reflexivity.
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_mpost (if from_primary n then 0 else 1) s (snd r)).
- intros [ob s2] H2. cbn [fst snd] in *. cbv zeta.
  destruct ob as [beg|]; cbv beta iota.
  + apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u3 s3] N3. cbn [fst snd] in *.
    apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s3 (snd r)).
    2:{ rk_if.
        - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; cbn [snd]; apply rk_nt_refl | apply rk_spin].
        - apply rk_ret. cbn [snd]. apply rk_nt_refl. }
    intros [u4 s4] N4. cbn [fst snd] in *. apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret. cbn [snd].
    apply (rk_mpost_nt_r _ _ s4); [|unfold rk_nt; rk_splits; reflexivity].
    apply (rk_mpost_nt_r _ _ s3); [|exact N4]. exact (rk_mpost_nt_r _ _ _ _ H2 N3).
  + apply rk_ret. cbn [snd]. exact H2.
- destruct (from_primary n) eqn:Fp; cbv beta iota.
  + pose proof (chunk_class_ok n Fp) as Hc.
    apply rk_bind.
    destruct (Z.eqb_spec (chunk_class n) kBatchClass) as [E24|N24].
    * rewrite E24, cache_alloc_cf_24. eapply ipost_mono; [|apply rk_cache_alloc24; exact I0].
      intros [o s2] (I2 & S2 & A2 & M2). cbn [fst snd] in *. apply rk_ret. cbn [snd].
      assert (Eb2 : errb_size_cf s2 = errb_size_cf s0) by (unfold errb_size_cf; rewrite S2; reflexivity).
      unfold rk_mpost. rewrite A2, Eb2, E0, A0. rewrite R0 in M2. split; [exact I2|]. split; [lia|]. split; [lia | exact M2].
    * eapply ipost_mono; [|apply rk_cache_alloc_cf_other; [lia | exact N24 | exact I0]].
      intros [o s2] (I2 & A2 & E2 & M2). cbn [fst snd] in *. apply rk_ret. cbn [snd].
      pose proof (exh_report_le_100 (chunk_class n) ltac:(lia)) as X.
      unfold rk_mpost. rewrite A2, A0, M2, R0. split; [exact I2|]. split; [lia|]. split; lia.
  + eapply ipost_mono; [|apply rk_sec_alloc; exact Fp]. intros [ob s2] (R2 & C2 & In2 & E2 & L2). cbn [fst snd] in *.
    unfold rk_mpost. split; [exact (rk_inv_frame _ _ I0 R2 C2 In2 E2)|].
    assert (Rg : reg s2 kBatchClass = reg s0 kBatchClass) by (unfold reg; rewrite R2; reflexivity).
    rewrite Rg, R0, E2, E0. rewrite A0 in L2. split; [lia|]. split; lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 11. The quarantine drain keeps every class's mapped size, adds no secondary   *)
(*     and leaves the error buffer as it is.                                      *)
Definition rk_fr (s s' : astate) : Prop :=
(forall x, rg_mapped_user (reg s' x) = rg_mapped_user (reg s x)) /\
(length (st_sec_arr s') <= length (st_sec_arr s))%nat /\ errb_size_cf s' = errb_size_cf s.

Lemma rk_fr_refl : forall s, rk_fr s s.
Proof. intros s. split; [intros x; reflexivity | split; [lia | reflexivity]]. Qed.
Lemma rk_fr_trans : forall s1 s2 s3, rk_fr s1 s2 -> rk_fr s2 s3 -> rk_fr s1 s3.
Proof. intros s1 s2 s3 (A1 & B1 & C1) (A2 & B2 & C2). split; [intros x; rewrite A2; apply A1 | split; [lia | congruence]]. Qed.
Lemma rk_fr_of_nt : forall s s', rk_nt s s' -> rk_fr s s'.
Proof.
intros s s' (A & B & C & D & E). split; [intros x; unfold reg; rewrite A; reflexivity|].
split; [rewrite E; lia|]. unfold errb_size_cf. rewrite D. reflexivity.
Qed.
Lemma rk_fr_set_region : forall s c r, rg_mapped_user r = rg_mapped_user (reg s c) ->
rk_fr s (set_regions (zupd c r (st_regions s)) s).
Proof. intros s c r H. split; [intros x; apply rk_reg_set_mapped; exact H | split; [cbn [st_sec_arr set_regions]; lia | reflexivity]]. Qed.
Lemma rk_fr_set_pc : forall s c p, rk_fr s (set_cache (zupd c p (st_cache s)) s).
Proof. intros s c p. split; [intros x; reflexivity | split; [cbn [st_sec_arr set_cache]; lia | reflexivity]]. Qed.

Lemma rk_efa_fr : forall c need sof s, ipost (ensure_free_array c need sof s) (fun r => rk_fr s (snd r)).
Proof.
intros c need sof s. unfold ensure_free_array. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply rk_fr_refl.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd]. apply rk_fr_set_region. reflexivity.
  + apply rk_bind. eapply ipost_mono with (P := fun r => rk_fr s (snd r)).
    2:{ destruct (aDestroyed z); cbv beta iota.
        - apply rk_set_region. cbn [snd]. apply rk_fr_set_region. reflexivity.
        - apply rk_ret. cbn [snd]. apply rk_fr_refl. }
    intros [u s1] H1. cbn [fst snd] in *. destruct sof; cbv beta iota; [apply rk_spin | apply rk_ret; exact H1].
Qed.

Lemma rk_rta_fr : forall c offs s, ipost (return_to_allocator c offs s) (fun r => rk_fr s (snd r)).
Proof.
intros c offs s. unfold return_to_allocator. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono; [|apply rk_efa_fr]. intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_set_region. cbn [snd].
eapply rk_fr_trans; [exact H1|]. apply rk_fr_set_region. reflexivity.
Qed.

Lemma rk_init_fr : forall s, ipost (init_cache_if_needed s) (fun r => rk_fr s (snd r)).
Proof.
intros s. unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (st_cache_inited s); cbv beta iota; [apply rk_ret | apply rk_put]; cbn [snd];
(split; [intros x; reflexivity | split; [apply Nat.le_refl | reflexivity]]).
Qed.

Lemma rk_cdealloc_fr : forall c off s, ipost (cache_dealloc c off s) (fun r => rk_fr s (snd r)).
Proof.
intros c off s. unfold cache_dealloc. cbv zeta. apply rk_bind. eapply ipost_mono; [|apply rk_init_fr].
intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_fr s1 (snd r)).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply rk_rta_fr]. intros [u2 s2] H2. cbn [fst snd] in *.
      apply rk_set_pc. cbn [snd]. eapply rk_fr_trans; [exact H2 | apply rk_fr_set_pc].
    - apply rk_ret. cbn [snd]. apply rk_fr_refl. }
intros [u3 s3] H3. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd]. apply rk_set_pc. cbn [snd].
eapply rk_fr_trans; [exact H1|]. eapply rk_fr_trans; [exact H3 | apply rk_fr_set_pc].
Qed.

Lemma rk_sdealloc_fr : forall r s, ipost (sec_dealloc r s) (fun x => rk_fr s (snd x)).
Proof.
intros r s. unfold sec_dealloc. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (nth_error (st_secs s) r) as [sm|] eqn:En; cbv beta iota; [|apply rk_fail].
destruct (index_of (st_sec_arr s) r 0%nat) as [i|]; cbv beta iota; [|apply rk_fail].
apply rk_bind. eapply ipost_mono with (P := fun x => snd x = s).
2:{ rk_if.
    - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; reflexivity | apply rk_spin].
    - apply rk_ret. reflexivity. }
intros [u s1] E1. cbn [fst snd] in *. subst s1.
apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. apply rk_modify. cbn [snd]. cbv zeta.
split; [intros x; reflexivity|]. split.
- cbn [st_sec_arr set_sec_arr]. pose proof (rk_removelast_le (lupd (st_sec_arr s) i (last (st_sec_arr s) r))) as L.
  rewrite lupd_length in L. exact L.
- rewrite !errb_size_first. cbn [st_secs set_sec_arr set_secs].
  apply (first_sz_lupd_same _ _ sm); [exact En | reflexivity | reflexivity].
Qed.

Lemma rk_rchunk_fr : forall k s, ipost (recycle_chunk k s) (fun r => rk_fr s (snd r)).
Proof.
intros k s. unfold recycle_chunk. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. apply rk_put. cbn [fst snd].
destruct (ck_beg k) as [|off|r o|cid pos]; cbv beta iota.
- apply rk_fail.
- eapply ipost_mono; [|apply rk_cdealloc_fr]. intros [u s1] H1. cbn [snd] in *.
  eapply rk_fr_trans; [|exact H1]. apply rk_fr_of_nt. unfold rk_nt. rk_splits; reflexivity.
- eapply ipost_mono; [|apply rk_sdealloc_fr]. intros [u s1] H1. cbn [snd] in *.
  eapply rk_fr_trans; [|exact H1]. apply rk_fr_of_nt. unfold rk_nt. rk_splits; reflexivity.
- apply rk_fail.
Qed.

Lemma rk_ritems_fr : forall fuel items s, ipost (recycle_items fuel items s) (fun r => rk_fr s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|k t] s; cbn [recycle_items].
- apply rk_ret. cbn [snd]. apply rk_fr_refl.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply rk_fr_refl.
- apply rk_bind. eapply ipost_mono; [|apply rk_rchunk_fr]. intros [u s1] H1. cbn [fst snd] in *.
  eapply ipost_mono; [|apply IH]. intros [u2 s2] H2. cbn [snd] in *. exact (rk_fr_trans _ _ _ H1 H2).
Qed.

Lemma rk_drecycle_fr : forall fuel bs s, ipost (do_recycle fuel bs s) (fun r => rk_fr s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|b t] s; cbn [do_recycle].
- apply rk_ret. cbn [snd]. apply rk_fr_refl.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply rk_fr_refl.
- apply rk_bind. eapply ipost_mono; [|apply rk_ritems_fr]. intros [u s1] H1. cbn [fst snd] in *.
  apply rk_bind. eapply ipost_mono; [|apply rk_cdealloc_fr]. intros [u2 s2] H2. cbn [fst snd] in *.
  eapply ipost_mono; [|apply IH]. intros [u3 s3] H3. cbn [snd] in *.
  exact (rk_fr_trans _ _ _ H1 (rk_fr_trans _ _ _ H2 H3)).
Qed.

Lemma rk_drain_fr : forall s, ipost (maybe_drain_cf s) (fun r => rk_fr s (snd r)).
Proof.
intros s. unfold maybe_drain_cf. cbv zeta. apply rk_bind. apply rk_get. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply rk_fr_refl.
- apply rk_bind. apply rk_put. cbn [fst snd].
  rk_if.
  + apply rk_ret. cbn [snd]. apply rk_fr_of_nt. unfold rk_nt. rk_splits; reflexivity.
  + do 2 (match goal with |- context [match ?x with _ => _ end] => destruct x end).
    apply rk_bind. apply rk_modify. cbn [fst snd].
    eapply ipost_mono; [|apply rk_drecycle_fr]. intros [u s3] H3. cbn [snd] in *.
    eapply rk_fr_trans; [|exact H3]. apply rk_fr_of_nt. unfold rk_nt. rk_splits; reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 12. free_cf.                                                                    *)
Lemma rk_enqueue : forall k s, room_shape_cf s -> ipost (enqueue k s) (fun r => st_secs (snd r) = st_secs s /\
st_sec_arr (snd r) = st_sec_arr s /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize).
Proof.
intros k s IV. assert (KU : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold enqueue. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s /\ st_sec_arr (snd r) = st_sec_arr s /\
  rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply rk_cache_alloc24; exact IV]. intros [ob s1] (_ & S1 & A1 & M1). cbn [fst snd] in *.
      destruct ob as [off|]; cbv beta iota; [apply rk_ret; cbn [snd]; rk_splits; assumption | apply rk_spin].
    - apply rk_ret. cbn [snd]. rk_splits; [reflexivity | reflexivity | lia]. }
intros [nb s2] (S2 & A2 & M2). cbn [fst snd] in *. apply rk_modify. cbn [snd]. rk_splits; assumption.
Qed.

Lemma rk_free_inner : forall p tr s, room_shape_cf s ->
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
(fun r => (length (st_sec_arr (snd r)) <= length (st_sec_arr s))%nat /\ errb_size_cf (snd r) = errb_size_cf s /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize).
Proof.
intros p tr s IV. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (find_user (st_chunks s) p) as [k|]; cbv beta iota; [|apply rk_fail].
apply rk_bind. eapply ipost_mono with (P := fun r => snd r = s).
2:{ destruct (ck_state k); cbv beta iota; [apply rk_ret; reflexivity | apply rk_fail]. }
intros [u3 s3] E3. cbn [fst snd] in *. subst s3.
apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u4 s4] N4. cbn [fst snd] in *. cbv zeta.
apply rk_bind. apply rk_modify. cbn [fst snd].
set (s5 := set_chunks (upd_chunk (st_chunks s4) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) s4).
assert (N5 : rk_nt s s5) by (eapply rk_nt_trans; [exact N4 | unfold rk_nt; rk_splits; reflexivity]).
apply rk_bind.
match goal with |- context [if ?c then _ else _] => destruct c end; cbv beta iota.
2:{ (* the recycle side of free_cf's size test *)
  eapply ipost_mono; [|apply rk_rchunk_fr]. intros [u6 s6] F6. cbn [fst snd] in *.
  eapply ipost_mono; [|apply rk_drain_fr]. intros [u7 s7] F7. cbn [snd] in *.
  pose proof (rk_fr_trans _ _ _ (rk_fr_of_nt _ _ N5) (rk_fr_trans _ _ _ F6 F7)) as (M & L & E).
  split; [exact L|]. split; [exact E|]. rewrite (M kBatchClass). unfold kUserMapSize. lia. }
eapply ipost_mono; [|apply rk_enqueue; exact (rk_nt_inv _ _ N5 IV)]. intros [u6 s6] (S6 & A6 & M6). cbn [fst snd] in *.
eapply ipost_mono; [|apply rk_drain_fr]. intros [u7 s7] (F7 & L7 & E7). cbn [snd] in *.
pose proof (rk_nt_meas _ _ N5) as (R5 & Eb5 & Sa5).
assert (Eb6 : errb_size_cf s6 = errb_size_cf s5) by (unfold errb_size_cf; rewrite S6; reflexivity).
rewrite (F7 kBatchClass). rewrite A6, Sa5 in L7. rewrite R5 in M6.
split; [exact L7|]. split; [congruence | exact M6].
Qed.

Theorem rk_free : forall p tr s, room_shape_cf s -> ipost (free_cf p tr s) (fun r =>
(length (st_sec_arr (snd r)) <= length (st_sec_arr s))%nat /\ errb_size_cf (snd r) = errb_size_cf s /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize).
Proof.
intros p tr s IV. assert (KU : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s (snd r)).
2:{ rk_if; [apply rk_ret; cbn [snd]; unfold rk_nt; rk_splits; reflexivity | apply rk_modify; cbn [snd]; unfold rk_nt; rk_splits; reflexivity]. }
intros [u s2] N2. cbn [fst snd] in *.
pose proof (rk_nt_inv _ _ N2 IV) as I2. pose proof (rk_nt_meas _ _ N2) as (R2 & E2 & A2).
destruct p as [|off|r o|cid pos]; cbv beta iota.
- apply rk_ret. cbn [snd]. rewrite R2, E2, A2. rk_splits; lia.
- eapply ipost_mono; [|apply (rk_free_inner (PPrim off) tr s2 I2)]. intros [u3 s3] (L & E & M). cbn [snd] in *.
  rewrite R2 in M. rewrite E2 in E. rewrite A2 in L. rk_splits; assumption.
- eapply ipost_mono; [|apply (rk_free_inner (PSec r o) tr s2 I2)]. intros [u3 s3] (L & E & M). cbn [snd] in *.
  rewrite R2 in M. rewrite E2 in E. rewrite A2 in L. rk_splits; assumption.
- eapply ipost_mono; [|apply (rk_free_inner (PFake cid pos) tr s2 I2)]. intros [u3 s3] (L & E & M). cbn [snd] in *.
  rewrite R2 in M. rewrite E2 in E. rewrite A2 in L. rk_splits; assumption.
Qed.

(* free_cf PNull, the entry step of the realloc tree: a frame. *)
Lemma rk_free_null : forall tr s, ipost (free_cf PNull tr s) (fun r => rk_nt s (snd r)).
Proof.
intros tr s. unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => rk_nt s (snd r)).
2:{ rk_if; [apply rk_ret; cbn [snd]; unfold rk_nt; rk_splits; reflexivity | apply rk_modify; cbn [snd]; unfold rk_nt; rk_splits; reflexivity]. }
intros [u s2] N2. cbn [fst snd] in *. apply rk_ret. cbn [snd]. exact N2.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 13. The realloc tree: free_cf PNull, malloc_cf, then free_cf on success.        *)
Theorem rk_realloc : forall p n tr s, room_shape_cf s -> ipost (realloc_tree_with malloc_cf free_cf p n tr s) (fun r =>
Z.of_nat (length (st_sec_arr (snd r))) <= Z.of_nat (length (st_sec_arr s)) + 1 /\
errb_size_cf (snd r) <= errb_size_cf s + 100 /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + 2 * kUserMapSize).
Proof.
intros p n tr s IV. assert (KU : 0 <= kUserMapSize) by (unfold kUserMapSize; lia).
unfold realloc_tree_with. apply rk_bind. eapply ipost_mono; [|apply rk_free_null]. intros [u s1] N1. cbn [fst snd] in *.
pose proof (rk_nt_inv _ _ N1 IV) as I1. pose proof (rk_nt_meas _ _ N1) as (R1 & E1 & A1).
apply rk_bind. eapply ipost_mono; [|apply rk_malloc; exact I1]. intros [q s2] (I2 & L2 & E2 & M2). cbn [fst snd] in *.
assert (Hb : (if from_primary n then 0 else 1) <= 1) by (destruct (from_primary n); lia).
assert (L2' : Z.of_nat (length (st_sec_arr s2)) <= Z.of_nat (length (st_sec_arr s1)) + 1) by lia.
rewrite A1 in L2'. rewrite E1 in E2. rewrite R1 in M2.
destruct q as [|off|r o|cid pos]; cbv beta iota.
- apply rk_ret. cbn [snd]. rk_splits; lia.
- apply rk_bind. eapply ipost_mono; [|apply rk_free; exact I2]. intros [u3 s3] (L3 & E3 & M3). cbn [fst snd] in *.
  apply rk_ret. cbn [snd]. rk_splits; lia.
- apply rk_bind. eapply ipost_mono; [|apply rk_free; exact I2]. intros [u3 s3] (L3 & E3 & M3). cbn [fst snd] in *.
  apply rk_ret. cbn [snd]. rk_splits; lia.
- apply rk_bind. eapply ipost_mono; [|apply rk_free; exact I2]. intros [u3 s3] (L3 & E3 & M3). cbn [fst snd] in *.
  apply rk_ret. cbn [snd]. rk_splits; lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 14. The step facts and the keep lemmas, over apath, with no gflag.              *)
Theorem malloc_step_cf : forall n tr s trc p s', room_shape_cf s -> apath (malloc_cf n tr s) trc (p, s') ->
room_shape_cf s' /\
Z.of_nat (length (st_sec_arr s')) <= Z.of_nat (length (st_sec_arr s)) + (if from_primary n then 0 else 1) /\
errb_size_cf s' <= errb_size_cf s + 100 /\
rg_mapped_user (reg s' kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize.
Proof. intros n tr s trc p s' IV Hp. exact (ipost_apath _ _ _ _ (rk_malloc n tr s IV) Hp). Qed.

Theorem free_step_cf : forall p tr s trc s', room_shape_cf s -> apath (free_cf p tr s) trc (tt, s') ->
(length (st_sec_arr s') <= length (st_sec_arr s))%nat /\ errb_size_cf s' = errb_size_cf s /\
rg_mapped_user (reg s' kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize.
Proof. intros p tr s trc s' IV Hp. exact (ipost_apath _ _ _ _ (rk_free p tr s IV) Hp). Qed.

Corollary malloc_room_shape_cf : forall n tr s trc p s', room_shape_cf s -> apath (malloc_cf n tr s) trc (p, s') ->
room_shape_cf s'.
Proof. intros n tr s trc p s' IV Hp. exact (proj1 (malloc_step_cf n tr s trc p s' IV Hp)). Qed.

Theorem malloc_room_keep_cf : forall k n tr s trc p s', room_shape_cf s ->
ROOM_cf_k s (Datatypes.S k) -> apath (malloc_cf n tr s) trc (p, s') -> ROOM_cf_k s' k.
Proof.
intros k n tr s trc p s' IV R Hp. destruct (malloc_step_cf n tr s trc p s' IV Hp) as (_ & L & E & M).
unfold ROOM_cf_k, ERRB_ROOM_k in *. unfold kUserMapSize, kFreeArrayOffset, kPage in *.
assert (Hb : 0 <= (if from_primary n then 0 else 1) <= 1) by (destruct (from_primary n); lia). lia.
Qed.

Theorem free_room_keep_cf : forall k p tr s trc s', room_shape_cf s ->
ROOM_cf_k s (Datatypes.S k) -> apath (free_cf p tr s) trc (tt, s') -> ROOM_cf_k s' k.
Proof.
intros k p tr s trc s' IV R Hp. destruct (free_step_cf p tr s trc s' IV Hp) as (L & E & M).
unfold ROOM_cf_k, ERRB_ROOM_k in *. unfold kUserMapSize, kFreeArrayOffset, kPage in *. lia.
Qed.

(* A realloc that returns a block is a malloc AND a free: two units. *)
Theorem realloc_room_keep_cf : forall k p n tr s trc q s', room_shape_cf s ->
ROOM_cf_k s (Datatypes.S (Datatypes.S k)) -> apath (realloc_tree_with malloc_cf free_cf p n tr s) trc (q, s') ->
ROOM_cf_k s' k.
Proof.
intros k p n tr s trc q s' IV R Hp. destruct (ipost_apath _ _ _ _ (rk_realloc p n tr s IV) Hp) as (L & E & M).
cbn [snd] in *. unfold ROOM_cf_k, ERRB_ROOM_k in *. unfold kUserMapSize, kFreeArrayOffset, kPage in *. lia.
Qed.

(* The refused arm (ReallocP's mt_refused): the entry free_cf PNull, then a malloc_cf: one unit. *)
Theorem realloc_room_keep_null_cf : forall k n tr s s', room_shape_cf s ->
ROOM_cf_k s (Datatypes.S k) -> mt_refused malloc_cf free_cf n tr s s' -> ROOM_cf_k s' k.
Proof.
intros k n tr s s' IV R (S1 & t1 & t2 & Hp1 & _ & Hp2 & _).
pose proof (ipost_apath _ _ _ _ (rk_free_null tr s) Hp1) as N1. cbn [snd] in N1.
pose proof (rk_nt_inv _ _ N1 IV) as I1. pose proof (rk_nt_meas _ _ N1) as (R1 & E1 & A1).
destruct (malloc_step_cf n tr S1 t2 PNull s' I1 Hp2) as (_ & L & E & M).
rewrite A1 in L. rewrite E1 in E. rewrite R1 in M.
unfold ROOM_cf_k, ERRB_ROOM_k in *. unfold kUserMapSize, kFreeArrayOffset, kPage in *.
assert (Hb : 0 <= (if from_primary n then 0 else 1) <= 1) by (destruct (from_primary n); lia). lia.
Qed.

End RS.

(* ---------------------------------------------------------------------------- *)
(* 15. The call-level steps: the leaves do not carry the model path, so the walk  *)
(*     passes the apath it holds (amreal_SRr04); room_shape_cf comes from the call   *)
(*     precondition's ARcf (amc_wf).                                               *)
Section STEP. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma room_shape_of_acall_pre_cf : forall segs B ly S Hp W regs mem md ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> room_shape_cf S.
Proof.
intros segs B ly S Hp W regs mem md ch H. pose proof (amc_wf _ _ _ _ _ (proj1 (proj1 H))) as W0. unfold Wf_cf in W0.
exact (room_shape_cf_of_WfP_cf _ _ _ _ _ W0).
Qed.

Lemma RK_malloc_step : forall segs B ly S Hp W regs mem md ch n tr trc r W' c' k,
acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf_k S (RK_malloc + k) ->
apath (malloc_cf n tr S) trc r -> malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' -> ROOM_cf_k (snd r) k.
Proof.
intros segs B ly S Hp W regs mem md ch n tr trc r W' c' k Hpre R Hpa _. destruct r as [p s'].
exact (malloc_room_keep_cf k n tr S trc p s' (room_shape_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) R Hpa).
Qed.

Lemma RK_free_step : forall segs B ly S Hp W regs mem md ch p n tr trc r W' c' k,
acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf_k S (RK_free + k) ->
apath (free_cf p tr S) trc r -> free_leaf_cf segs B ly S Hp W regs mem md p n r W' c' -> ROOM_cf_k (snd r) k.
Proof.
intros segs B ly S Hp W regs mem md ch p n tr trc r W' c' k Hpre R Hpa _. destruct r as [[] s'].
exact (free_room_keep_cf k p tr S trc s' (room_shape_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) R Hpa).
Qed.

Lemma RK_realloc_step : forall segs B ly S Hp W regs mem md ch p n_old n tr trc r W' c' k,
acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf_k S (RK_realloc + k) ->
apath (realloc_tree_with malloc_cf free_cf p n tr S) trc r ->
realloc_leaf_cf segs B ly S Hp W regs mem md p n_old n r W' c' -> ROOM_cf_k (snd r) k.
Proof.
intros segs B ly S Hp W regs mem md ch p n_old n tr trc r W' c' k Hpre R Hpa _. destruct r as [q s'].
exact (realloc_room_keep_cf k p n tr S trc q s' (room_shape_of_acall_pre_cf _ _ _ _ _ _ _ _ _ _ Hpre) R Hpa).
Qed.

End STEP.
