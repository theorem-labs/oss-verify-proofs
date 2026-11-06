(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepModel2cf.v (commit f01d79f3fb5, cf refill round 3; file sha256 6161557ead7e) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, RepF1Leaf): model lemmas of the class-full report arm, at the MODEL
   level only (itree / astate): no machine, no symbolic execution, no address.
   rule 24: proves no function (kind: model lemma).
   (1) [amreal_ibind_ipost]: amreal (YG0d.v:66-85) of [ibind t k] depends on k only at the results that t can
       return, so two continuations that agree on every result allowed by cfx_ipost (YGcfXs.v:301) are exchangeable.
   (2) [only_secs]: errb_append_cf (YG00cf.v:133-143) changes the state only in st_secs and in the event counter
       (the tick of errb_map_cf, YG00cf.v:122-127); [append_only_secs] and the field projections.
   (3) [xs_same] / [errb_room]: errb_append_cf keeps the errbuf extent of xs_cf (YG0ncf.v:102-106) when it does
       not remap ([append_keeps_xs]: errb_set_size, YG00cf.v:91-96, replaces the size entry in place or appends one,
       and neither is a capacity entry), and the first of two appends either keeps it or leaves room for the second
       ([append_first]); [xs_cf_same] carries the extent across a layout step (layout_le, YG0f.v:63-68).
   (4) exh_set (RepModelcf.v:34-37), the state shift of set_exh_cf: its fields, the class's flag, and the invariant
       after the shift ([wfp_exh_set], from set_exh_ret_cf_ok, YG06cf.v:228-242).
   The event counter is never named here (the event-term gate): [only_secs] fixes it by an existential, and
   [exh_set_regions_only] states that exh_set changes st_regions only. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstRefill.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG01cf YG06cf YG0ncf YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RepModelcf RepIFcf.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* (1) Continuations that agree on the returned results.                         *)
Lemma amreal_ibind_ipost : forall segs {A B} (t : itree astate A) (P : A -> Prop) (k0 k1 : A -> itree astate B) W c Q,
  YGcfXs.cfx_ipost t P -> (forall r, P r -> k1 r = k0 r) -> amreal segs (ibind t k1) W c Q -> amreal segs (ibind t k0) W c Q.
Proof.
intros segs A B t P k0 k1 W c Q Hp Hk. revert Hp W c.
induction t as [a | q s k IH | pc | f]; intros Hp W c H; cbn [ibind cfx_ipost] in Hp, H |- *.
- rewrite <- (Hk a Hp). exact H.
- cbn [amreal] in H |- *. eapply SRr_mono; [exact H |]. intros W1 c1 _ Hx. destruct q;
  try (destruct Hx as (J & nx & bit & sp & i0 & Hn & Ht & Hb0 & Hsp & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
  split; [exact Hn|]; split; [exact Ht|]; split; [exact Hb0|]; split; [exact Hsp|];
  split; [exact Hb|]; split; [exact Hr|]; split; [exact Hz|]; intros i Hi; exact (IH _ (Hp _) _ _ (Hc i Hi))).
  destruct Hx as (z & Hz & Hc). exists z. split; [exact Hz|]. exact (IH _ (Hp z) _ _ Hc).
- exact H.
- exact I.
Qed.

(* ---------------------------------------------------------------------------- *)
(* (2) The append changes st_secs and the event counter only.                    *)
Definition only_secs (s s' : astate) : Prop := exists n, s' = set_nev n (set_secs (st_secs s') s).

Lemma only_secs_refl : forall s, only_secs s s.
Proof. intros s. destruct s. eexists. reflexivity. Qed.

Lemma only_secs_trans : forall s s' s'', only_secs s s' -> only_secs s' s'' -> only_secs s s''.
Proof.
intros s s' s'' [n E1] [m E2]. exists m.
transitivity (set_nev m (set_secs (st_secs s'') s')); [exact E2 |]. rewrite E1. reflexivity.
Qed.

Lemma only_secs_fields : forall s s', only_secs s s' ->
  st_regions s' = st_regions s /\ st_cache s' = st_cache s /\ st_chunks s' = st_chunks s /\
  st_cache_inited s' = st_cache_inited s /\ st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\
  st_fs s' = st_fs s /\ st_sec_arr s' = st_sec_arr s.
Proof. intros s s' [n E]. rewrite E. repeat split. Qed.

Lemma only_secs_regions : forall s s', only_secs s s' -> st_regions s' = st_regions s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.
Lemma only_secs_st_cache : forall s s', only_secs s s' -> st_cache s' = st_cache s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.
Lemma only_secs_chunks : forall s s', only_secs s s' -> st_chunks s' = st_chunks s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.
Lemma only_secs_cache_inited : forall s s', only_secs s s' -> st_cache_inited s' = st_cache_inited s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.
Lemma only_secs_qthread : forall s s', only_secs s s' -> st_qthread s' = st_qthread s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.
Lemma only_secs_qglobal : forall s s', only_secs s s' -> st_qglobal s' = st_qglobal s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.
Lemma only_secs_fs : forall s s', only_secs s s' -> st_fs s' = st_fs s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.
Lemma only_secs_sec_arr : forall s s', only_secs s s' -> st_sec_arr s' = st_sec_arr s.
Proof. intros s s' H. apply (only_secs_fields s s' H). Qed.

Lemma only_secs_reg : forall s s' c, only_secs s s' -> reg s' c = reg s c.
Proof. intros s s' c H. unfold reg. rewrite (only_secs_regions s s' H). reflexivity. Qed.
Lemma only_secs_cache : forall s s' c, only_secs s s' -> cache s' c = cache s c.
Proof. intros s s' c H. unfold cache. rewrite (only_secs_st_cache s s' H). reflexivity. Qed.
Lemma only_secs_exh_mem : forall s s' c, only_secs s s' -> exh_mem_cf s' c = exh_mem_cf s c.
Proof. intros s s' c H. unfold exh_mem_cf. rewrite (only_secs_reg s s' c H). reflexivity. Qed.
(* qloose (YG01.v:229-230) reads the two quarantine caches and st_chunks only. *)
Lemma only_secs_qloose : forall s s', only_secs s s' -> (qloose s' <-> qloose s).
Proof. intros s s' [n E]. rewrite E. reflexivity. Qed.

Lemma ipost_bind : forall {A B} (m : M A) (k : A -> M B) s (P : B * astate -> Prop),
  cfx_ipost (m s) (fun r => cfx_ipost (k (fst r) (snd r)) P) -> cfx_ipost (bind m k s) P.
Proof.
intros A B m k s P H. unfold bind. apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact H].
intros [a s'] Ha. exact Ha.
Qed.

(* A step that keeps [only_secs s0] from every state that has it. *)
Definition os_step {A : Type} (m : M A) : Prop :=
  forall s0 s, only_secs s0 s -> cfx_ipost (m s) (fun r => only_secs s0 (snd r)).

Lemma os_bind : forall {A B} (m : M A) (k : A -> M B), os_step m -> (forall a, os_step (k a)) -> os_step (bind m k).
Proof.
intros A B m k Hm Hk s0 s H. apply ipost_bind. eapply cfx_ipost_mono; [|exact (Hm s0 s H)].
intros [a s1] H1. exact (Hk a s0 s1 H1).
Qed.

Lemma os_get : forall {B} (k : astate -> M B), (forall x, os_step (k x)) -> os_step (bind get k).
Proof. intros B k Hk s0 s H. exact (Hk s s0 s H). Qed.

Lemma os_ret : forall {A} (a : A), os_step (ret a).
Proof. intros A a s0 s H. exact H. Qed.

Lemma os_spin : forall {A} pc, os_step (@spin A pc).
Proof. intros A pc s0 s H. exact I. Qed.

Lemma os_askz : forall q, os_step (askz q).
Proof. intros q s0 s H z. exact H. Qed.

Lemma os_set_secs : forall s0 s v, only_secs s0 s -> only_secs s0 (set_secs v s).
Proof.
intros s0 s v [n E]. exists n. transitivity (set_secs v s); [reflexivity|]. rewrite E. reflexivity.
Qed.

Lemma os_set_nev : forall s0 s k, only_secs s0 s -> only_secs s0 (set_nev k s).
Proof.
intros s0 s k [n E]. exists k. transitivity (set_nev k s); [reflexivity|]. rewrite E. reflexivity.
Qed.

Lemma os_tick : os_step tick.
Proof. intros s0 s H. apply os_set_nev. exact H. Qed.

Lemma os_retire : os_step errb_retire.
Proof. intros s0 s H. apply os_set_secs. exact H. Qed.

Lemma os_set_size : forall ns, os_step (errb_set_size ns).
Proof.
intros ns s0 s H. unfold errb_set_size, modify. cbn [cfx_ipost snd].
destruct (find_sz (st_secs s) 0); apply os_set_secs; exact H.
Qed.

Lemma os_map : forall want, os_step (errb_map_cf want).
Proof.
intros want. unfold errb_map_cf. cbv zeta.
apply os_bind; [exact os_tick | intros u].
apply os_bind; [apply os_askz | intros z].
destruct (z =? 0); [apply os_spin |].
apply os_bind; [exact os_retire | intros u'].
intros s0 s H. apply os_set_secs. exact H.
Qed.

Lemma os_append : forall L, os_step (errb_append_cf L).
Proof.
intros L. unfold errb_append_cf. apply os_get. intros x.
destruct (negb (errb_mapped_cf x)).
- apply os_bind; [apply os_map | intros u]. apply os_get. intros x1.
  apply os_bind; [| intros u'; apply os_set_size].
  destruct (errb_cap_cf x1 <? L); [apply os_map | apply os_ret].
- cbv zeta. apply os_bind; [| intros u; apply os_set_size].
  destruct (errb_cap_cf x <? errb_size_cf x + L); [apply os_map | apply os_ret].
Qed.

Lemma append_only_secs : forall L s, YGcfXs.cfx_ipost (errb_append_cf L s) (fun r => only_secs s (snd r)).
Proof. intros L s. exact (os_append L s s (only_secs_refl s)). Qed.

(* ---------------------------------------------------------------------------- *)
(* (3) The errbuf extent across an append.                                       *)
Definition xs_same (s s' : astate) : Prop :=
  last_cap_idx (st_secs s') 0 None = last_cap_idx (st_secs s) 0 None /\ errb_cap_cf s' = errb_cap_cf s.
Definition errb_room (L : Z) (s : astate) : Prop := errb_mapped_cf s = true /\ errb_size_cf s + L <= errb_cap_cf s.

Lemma rm2_existsb_filter : forall {X} (f : X -> bool) l,
  existsb f l = match filter f l with [] => false | _ => true end.
Proof.
intros X f l. induction l as [|x t IH]; [reflexivity|]. cbn [existsb filter].
destruct (f x); [reflexivity | exact IH].
Qed.

Lemma rm2_find_sz_ge : forall l k i, find_sz l k = Some i -> (k <= i)%nat.
Proof.
induction l as [|sm t IH]; intros k i H; cbn [find_sz] in H; [discriminate H|].
destruct (is_errb_sz sm); [injection H as <-; lia | specialize (IH _ _ H); lia].
Qed.

Lemma rm2_sz_not_cap : forall sm, is_errb_sz sm = true -> is_errb_cap sm = false.
Proof.
intros sm H. unfold is_errb_sz, is_errb_cap, ERRB_SZ_TAG, ERRB_CAP_TAG in *.
apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma rm2_find_sz_upd : forall l k i v, find_sz l k = Some i -> is_errb_cap v = false ->
  filter is_errb_cap (lupd l (i - k) v) = filter is_errb_cap l /\
  (forall acc, last_cap_idx (lupd l (i - k) v) k acc = last_cap_idx l k acc).
Proof.
induction l as [|sm t IH]; intros k i v H Hv; cbn [find_sz] in H; [discriminate H|].
destruct (is_errb_sz sm) eqn:Es.
- injection H as <-. rewrite Nat.sub_diag. cbn [lupd filter last_cap_idx].
  rewrite Hv, (rm2_sz_not_cap sm Es). split; [reflexivity | intros acc; reflexivity].
- pose proof (rm2_find_sz_ge _ _ _ H) as Hge.
  replace (i - k)%nat with (S (i - S k)) by lia. cbn [lupd filter last_cap_idx].
  destruct (IH (S k) i v H Hv) as [F L]. rewrite F. split; [reflexivity | intros acc; apply L].
Qed.

Lemma rm2_last_cap_app1 : forall l k acc x, is_errb_cap x = false -> last_cap_idx (l ++ [x]) k acc = last_cap_idx l k acc.
Proof.
induction l as [|sm t IH]; intros k acc x Hx; cbn [app last_cap_idx].
- rewrite Hx. reflexivity.
- apply IH. exact Hx.
Qed.

Lemma rm2_filter_app1 : forall l x, is_errb_cap x = false -> filter is_errb_cap (l ++ [x]) = filter is_errb_cap l.
Proof. intros l x Hx. rewrite filter_app. cbn [filter]. rewrite Hx. apply app_nil_r. Qed.

Lemma rm2_find_sz_upd_get : forall l k i v, find_sz l k = Some i -> is_errb_sz v = true ->
  find_sz (lupd l (i - k) v) k = Some i /\ nth_error (lupd l (i - k) v) (i - k) = Some v.
Proof.
induction l as [|sm t IH]; intros k i v H Hv; cbn [find_sz] in H; [discriminate H|].
destruct (is_errb_sz sm) eqn:Es.
- injection H as <-. rewrite Nat.sub_diag. cbn [lupd find_sz nth_error]. rewrite Hv. split; reflexivity.
- pose proof (rm2_find_sz_ge _ _ _ H) as Hge.
  replace (i - k)%nat with (S (i - S k)) by lia. cbn [lupd find_sz nth_error]. rewrite Es.
  exact (IH (S k) i v H Hv).
Qed.

Lemma rm2_find_sz_app1 : forall l k v, find_sz l k = None -> is_errb_sz v = true ->
  find_sz (l ++ [v]) k = Some (k + length l)%nat.
Proof.
induction l as [|sm t IH]; intros k v H Hv; cbn [find_sz app length] in *.
- rewrite Hv. f_equal. lia.
- destruct (is_errb_sz sm); [discriminate H|]. rewrite (IH (S k) v H Hv). f_equal. lia.
Qed.

(* The state errb_set_size ns writes (YG00cf.v:91-96). *)
Definition sz_set (ns : Z) (s : astate) : astate :=
  match find_sz (st_secs s) 0 with
  | Some i => set_secs (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false)) s
  | None => set_secs (st_secs s ++ [mkSec ns ERRB_SZ_TAG false]) s
  end.

Lemma errb_set_size_eq : forall ns s, errb_set_size ns s = IRet (tt, sz_set ns s).
Proof. intros ns s. reflexivity. Qed.

Lemma sz_set_filter : forall ns s, filter is_errb_cap (st_secs (sz_set ns s)) = filter is_errb_cap (st_secs s).
Proof.
intros ns s. unfold sz_set. destruct (find_sz (st_secs s) 0) as [i|] eqn:E; cbn [st_secs set_secs].
- pose proof (rm2_find_sz_upd _ _ _ (mkSec ns ERRB_SZ_TAG false) E eq_refl) as [F _].
  rewrite Nat.sub_0_r in F. exact F.
- apply rm2_filter_app1. reflexivity.
Qed.

Lemma sz_set_lci : forall ns s, last_cap_idx (st_secs (sz_set ns s)) 0 None = last_cap_idx (st_secs s) 0 None.
Proof.
intros ns s. unfold sz_set. destruct (find_sz (st_secs s) 0) as [i|] eqn:E; cbn [st_secs set_secs].
- pose proof (rm2_find_sz_upd _ _ _ (mkSec ns ERRB_SZ_TAG false) E eq_refl) as [_ L].
  rewrite Nat.sub_0_r in L. apply L.
- apply rm2_last_cap_app1. reflexivity.
Qed.

Lemma sz_set_cap : forall ns s, errb_cap_cf (sz_set ns s) = errb_cap_cf s.
Proof. intros ns s. unfold errb_cap_cf, errb_e. rewrite sz_set_filter. reflexivity. Qed.

Lemma sz_set_mapped : forall ns s, errb_mapped_cf (sz_set ns s) = errb_mapped_cf s.
Proof. intros ns s. unfold errb_mapped_cf. rewrite !rm2_existsb_filter, sz_set_filter. reflexivity. Qed.

Lemma sz_set_size : forall ns s, errb_size_cf (sz_set ns s) = ns.
Proof.
intros ns s. unfold errb_size_cf, sz_set. destruct (find_sz (st_secs s) 0) as [i|] eqn:E; cbn [st_secs set_secs].
- pose proof (rm2_find_sz_upd_get _ _ _ (mkSec ns ERRB_SZ_TAG false) E eq_refl) as [F N].
  rewrite Nat.sub_0_r in F, N. rewrite F, N. reflexivity.
- rewrite (rm2_find_sz_app1 _ _ (mkSec ns ERRB_SZ_TAG false) E eq_refl). cbn [Nat.add].
  rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
Qed.

Lemma rm2_retire_filter : forall l,
  filter is_errb_cap (map (fun sm => if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm) l) = [].
Proof.
induction l as [|sm t IH]; [reflexivity|]. cbn [map filter].
destruct (is_errb_cap sm) eqn:E; [exact IH | rewrite E; exact IH].
Qed.

(* Every returning path of a (re)map ends with exactly one current capacity entry, of the rounded size. *)
Lemma map_post : forall want s, cfx_ipost (errb_map_cf want s)
  (fun r => errb_mapped_cf (snd r) = true /\ errb_cap_cf (snd r) = Z.max 0 (round_up want kPage)).
Proof.
intros want s. unfold errb_map_cf. cbv zeta. apply ipost_bind. cbn [tick modify cfx_ipost fst snd].
apply ipost_bind. unfold askz. cbn [cfx_ipost]. intros z. cbn [cfx_ipost fst snd].
destruct (z =? 0); [exact I|]. apply ipost_bind. unfold errb_retire, modify. cbn [cfx_ipost fst snd st_secs set_secs].
split.
- unfold errb_mapped_cf. cbn [st_secs set_secs]. rewrite existsb_app. apply orb_true_iff. right. reflexivity.
- unfold errb_cap_cf, errb_e. cbn [st_secs set_secs]. rewrite filter_app, rm2_retire_filter. reflexivity.
Qed.

Lemma bind_ret_l : forall {A B} (a : A) (k : A -> M B) s, bind (ret a) k s = k a s.
Proof. reflexivity. Qed.

Lemma append_keeps_xs : forall L s, 0 <= L -> errb_room L s ->
  YGcfXs.cfx_ipost (errb_append_cf L s) (fun r => xs_same s (snd r)).
Proof.
intros L s HL [Hm Hr]. unfold errb_append_cf. rewrite rep_bind_get. cbv beta. rewrite Hm. cbn [negb]. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hr). rewrite bind_ret_l, errb_set_size_eq. cbn [cfx_ipost snd].
split; [apply sz_set_lci | apply sz_set_cap].
Qed.

(* Unmapped: the map of ERRB_INIT = 65536 bytes. Mapped without room: the remap to
   round_up (size + L1) kPage = cap + kPage, since cap is a multiple of kPage and
   cap < size + L1 <= cap + kPage. Either way at least L2 bytes stay free. *)
Lemma append_first : forall L1 L2 s, 0 <= L1 -> 0 <= L2 -> L1 + L2 <= kPage ->
  errb_size_cf s <= errb_cap_cf s -> errb_cap_cf s mod kPage = 0 ->
  YGcfXs.cfx_ipost (errb_append_cf L1 s) (fun r => xs_same s (snd r) \/ errb_room L2 (snd r)).
Proof.
intros L1 L2 s H1 H2 H12 Hsc Hal.
destruct (errb_mapped_cf s) eqn:Em.
- destruct (Z.leb_spec (errb_size_cf s + L1) (errb_cap_cf s)) as [Hle|Hgt].
  + eapply cfx_ipost_mono; [| exact (append_keeps_xs L1 s H1 (conj Em Hle))].
    intros r Hr. left. exact Hr.
  + unfold errb_append_cf. rewrite rep_bind_get. cbv beta. rewrite Em. cbn [negb]. cbv zeta.
    rewrite (proj2 (Z.ltb_lt _ _) Hgt). apply ipost_bind.
    eapply cfx_ipost_mono; [| exact (map_post (errb_size_cf s + L1) s)].
    intros [u s1] [Hm1 Hc1]. cbn [fst snd] in Hm1, Hc1 |- *. rewrite errb_set_size_eq. cbn [cfx_ipost snd].
    right. split; [rewrite sz_set_mapped; exact Hm1 |].
    rewrite sz_set_size, sz_set_cap, Hc1.
    pose proof (errb_cap_cf_nonneg s) as Hc0.
    rewrite (round_up_step (errb_size_cf s + L1) (errb_cap_cf s) kPage); [| unfold kPage; lia | exact Hal | unfold kPage in *; lia].
    unfold kPage in *. lia.
- unfold errb_append_cf. rewrite rep_bind_get. cbv beta. rewrite Em. cbn [negb].
  apply ipost_bind. eapply cfx_ipost_mono; [| exact (map_post ERRB_INIT s)].
  intros [u s1] [Hm1 Hc1]. cbn [fst snd] in Hm1, Hc1 |- *.
  assert (Hc1' : errb_cap_cf s1 = 65536) by (rewrite Hc1; reflexivity).
  rewrite rep_bind_get. cbv beta. rewrite Hc1'.
  rewrite (proj2 (Z.ltb_ge _ _)) by (unfold kPage in *; lia).
  rewrite bind_ret_l, errb_set_size_eq. cbn [cfx_ipost snd].
  right. split; [rewrite sz_set_mapped; exact Hm1 |].
  rewrite sz_set_size, sz_set_cap, Hc1'. unfold kPage in *. lia.
Qed.

Lemma rm2_last_cap_idx_lt : forall l k acc i, last_cap_idx l k acc = Some i ->
  acc = Some i \/ (k <= i < k + length l)%nat.
Proof.
induction l as [|sm t IH]; intros k acc i H; cbn [last_cap_idx length] in *.
- left. exact H.
- destruct (IH (S k) _ i H) as [E|E]; [| right; lia].
  destruct (is_errb_cap sm); [injection E as <-; right; lia | left; exact E].
Qed.

Lemma last_cap_idx_lt : forall l i, last_cap_idx l 0 None = Some i -> (i < length l)%nat.
Proof. intros l i H. destruct (rm2_last_cap_idx_lt l 0 None i H) as [E|E]; [discriminate E | lia]. Qed.

Lemma xs_cf_same : forall ly ly' s s', xs_same s s' -> layout_le (length (st_secs s)) ly ly' ->
  YG0ncf.xs_cf ly' s' = YG0ncf.xs_cf ly s.
Proof.
intros ly ly' s s' [E1 E2] HL. unfold xs_cf. rewrite E1, E2.
destruct (last_cap_idx (st_secs s) 0 None) as [i|] eqn:E; [|reflexivity].
destruct HL as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&HS). rewrite (HS i (last_cap_idx_lt _ _ E)). reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* (4) The shift exh_set.                                                        *)
Lemma rm2_nth_lupd_other {X : Type} : forall (l : list X) i j v d, i <> j -> nth j (lupd l i v) d = nth j l d.
Proof. induction l as [|h t IH]; intros [|i] [|j] v d Hij; cbn [lupd nth]; auto; try congruence. Qed.

(* exh_set changes st_regions only (so it keeps the event counter too). *)
Lemma exh_set_regions_only : forall c S, exh_set c S = set_regions (st_regions (exh_set c S)) S.
Proof. intros c S. reflexivity. Qed.

Lemma exh_set_fields : forall c S,
  st_secs (exh_set c S) = st_secs S /\ st_cache (exh_set c S) = st_cache S /\ st_chunks (exh_set c S) = st_chunks S /\
  st_cache_inited (exh_set c S) = st_cache_inited S /\ st_qthread (exh_set c S) = st_qthread S /\
  st_qglobal (exh_set c S) = st_qglobal S /\ st_fs (exh_set c S) = st_fs S /\ st_sec_arr (exh_set c S) = st_sec_arr S.
Proof. intros c S. repeat split. Qed.

Lemma exh_set_reg_same : forall c S, (Z.to_nat c < length (st_regions S))%nat ->
  reg (exh_set c S) c = mkRegion (rg_mapped_user (reg S c)) (rg_alloc_user (reg S c)) (rg_mapped_fa (reg S c))
                                 (rg_free (reg S c)) (add_hole (EXH_HOLE, 0) (rg_holes (reg S c))).
Proof.
intros c S Hl. unfold exh_set, upd_reg. unfold reg at 1. cbn [st_regions set_regions]. unfold znth, zupd.
apply nth_lupd_same. exact Hl.
Qed.

Lemma exh_set_reg_other : forall c c' S, 1 <= c -> c' <> c -> reg (exh_set c S) c' = reg S c'.
Proof.
intros c c' S Hc Hne. unfold exh_set, upd_reg. unfold reg at 1. cbn [st_regions set_regions]. unfold znth, zupd.
apply rm2_nth_lupd_other. lia.
Qed.

Lemma exh_set_mapped_user : forall c S, (Z.to_nat c < length (st_regions S))%nat ->
  rg_mapped_user (reg (exh_set c S) c) = rg_mapped_user (reg S c).
Proof. intros c S Hl. rewrite (exh_set_reg_same c S Hl). reflexivity. Qed.
Lemma exh_set_alloc_user : forall c S, (Z.to_nat c < length (st_regions S))%nat ->
  rg_alloc_user (reg (exh_set c S) c) = rg_alloc_user (reg S c).
Proof. intros c S Hl. rewrite (exh_set_reg_same c S Hl). reflexivity. Qed.
Lemma exh_set_mapped_fa : forall c S, (Z.to_nat c < length (st_regions S))%nat ->
  rg_mapped_fa (reg (exh_set c S) c) = rg_mapped_fa (reg S c).
Proof. intros c S Hl. rewrite (exh_set_reg_same c S Hl). reflexivity. Qed.
Lemma exh_set_free : forall c S, (Z.to_nat c < length (st_regions S))%nat ->
  rg_free (reg (exh_set c S) c) = rg_free (reg S c).
Proof. intros c S Hl. rewrite (exh_set_reg_same c S Hl). reflexivity. Qed.

Lemma exh_set_mem : forall c c' S, 1 <= c -> (Z.to_nat c < length (st_regions S))%nat ->
  exh_mem_cf (exh_set c S) c' = (if c' =? c then true else exh_mem_cf S c').
Proof.
intros c c' S Hc Hl. destruct (Z.eqb_spec c' c) as [->|Hne].
- unfold exh_mem_cf. rewrite (exh_set_reg_same c S Hl). reflexivity.
- unfold exh_mem_cf. rewrite (exh_set_reg_other c c' S Hc Hne). reflexivity.
Qed.

Lemma exh_set_qloose : forall c S, qloose (exh_set c S) <-> qloose S.
Proof. intros c S. reflexivity. Qed.

Lemma exh_set_slack : forall c S, errb_slack (exh_set c S) = errb_slack S.
Proof. intros c S. reflexivity. Qed.

Lemma wfp_exh_set : forall U S c, 1 <= c <= 31 -> exh_mem_cf S c = false -> WfP_cf U 1 1 0 S ->
  WfP_cf U 0 (errb_slack (exh_set c S)) 0 (exh_set c S).
Proof.
intros U S c Hc _ W.
pose proof (set_exh_ret_cf_ok U 1 1 0 S c true W Hc) as H.
change ((set_exh_cf c ;; ret false) S) with (@IRet astate (bool * astate) (false, exh_set c S)) in H.
cbn [atok] in H. unfold exh_post_cf in H. destruct H as [_ (r' & _ & W' & _)].
apply (WfP_cf_weaken U 1 1 0); [exact W' | lia | | lia].
unfold errb_slack. destruct (find_sz (st_secs (exh_set c S)) 0); lia.
Qed.

End a.
