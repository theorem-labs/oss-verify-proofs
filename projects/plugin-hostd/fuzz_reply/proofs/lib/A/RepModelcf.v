(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepModelcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 e2c07001688b) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* The class-full report of the cf allocator instance, at the MODEL level only (itree / astate): no machine, no
   symbolic execution, no address.
   rule 24: proves no function (kind: model and invariant lemmas).
   (1) [exh_set]: the state shift of set_exh_cf (YG00cf.v:38-41), and [set_exh_cf_eq].  upd_reg is YG06.v:11.
   (2) [tsim]: two trees that differ only in the snapshots their IAsk nodes carry.  amreal (YG0d.v:66-85) reads a
       snapshot only through aok (YG00.v:593-599), so [amreal_tsim] carries amreal across [tsim]; [tsim_bind] composes
       it; [tsim_append_exh]: errb_append_cf (YG00cf.v:133-143) touches st_secs only and asks only KMmapSec, whose aok
       does not read the state, so shifting the state by [exh_set c] commutes with it.
   (3) [tree_classfull_cf]: the cf refill tree (YGcfInstRefill.v:58) on a non-batch class whose user map would cross
       kFreeArrayOffset is the two report appends followed by the shift (YG00cf.v:147-178, :181-224), and
       [amreal_classfull_shift] moves the shift in front of the appends for amreal.
   The equation of (3) reassociates ibind under IAsk continuations, so it uses Stdlib's functional_extensionality. *)
(* Built against the report interface at RepIFcf 2d6dcb3547a (errb_call_pre's lk / errb_slack). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstRefill.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* (1) The state shift.                                                          *)
Definition exh_set (c : Z) (s : astate) : astate :=
  let r := reg s c in
  upd_reg c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
                      (add_hole (EXH_HOLE, 0) (rg_holes r))) s.

Lemma set_exh_cf_eq : forall c s, set_exh_cf c s = IRet (tt, exh_set c s).
Proof. intros c s. reflexivity. Qed.

Lemma rep_exh_secs : forall c s, st_secs (exh_set c s) = st_secs s.
Proof. intros c s. reflexivity. Qed.

Lemma rep_exh_set_secs : forall c v s, set_secs v (exh_set c s) = exh_set c (set_secs v s).
Proof. intros c v s. destruct s. reflexivity. Qed.

Lemma rep_exh_mapped : forall c s, errb_mapped_cf (exh_set c s) = errb_mapped_cf s.
Proof. intros c s. unfold errb_mapped_cf. rewrite rep_exh_secs. reflexivity. Qed.

Lemma rep_exh_cap : forall c s, errb_cap_cf (exh_set c s) = errb_cap_cf s.
Proof. intros c s. unfold errb_cap_cf, errb_e. rewrite rep_exh_secs. reflexivity. Qed.

Lemma rep_exh_size : forall c s, errb_size_cf (exh_set c s) = errb_size_cf s.
Proof. intros c s. unfold errb_size_cf. rewrite rep_exh_secs. reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)
(* (2) Snapshot-blind simulation.                                                *)
Inductive tsim {A : Type} (R : A -> A -> Prop) : itree astate A -> itree astate A -> Prop :=
| tsim_ret : forall r0 r1, R r0 r1 -> tsim R (IRet r0) (IRet r1)
| tsim_ask : forall q s0 s1 k0 k1, (forall z, aok s1 q z -> aok s0 q z) ->
             (forall z, tsim R (k0 z) (k1 z)) -> tsim R (IAsk q s0 k0) (IAsk q s1 k1)
| tsim_spin : forall pc, tsim R (ISpin pc) (ISpin pc)
| tsim_fail : forall f t1, tsim R (IFail f) t1.

Lemma amreal_tsim : forall segs {A} (R : A -> A -> Prop) (t0 t1 : itree astate A) W c Q0 Q1,
  tsim R t0 t1 -> (forall r0 r1 W' c', R r0 r1 -> Q1 r1 W' c' -> Q0 r0 W' c') ->
  amreal segs t1 W c Q1 -> amreal segs t0 W c Q0.
Proof.
intros segs A R t0 t1 W c Q0 Q1 Hs HQ. revert W c.
induction Hs as [r0 r1 Hr | q s0 s1 k0 k1 Ha Hk IH | pc | f tx]; intros W c H; cbn in *.
- eapply SRr_mono; [exact H | intros W' c' _ H'; exact (HQ r0 r1 W' c' Hr H')].
- eapply SRr_mono; [exact H |]. intros W1 c1 _ Hx. destruct q;
  try (destruct Hx as (J & nx & bit & sp & i0 & Hn & Ht & Hb0 & Hsp & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
  split; [exact Hn|]; split; [exact Ht|]; split; [intros i; exact (Ha _ (Hb0 i))|]; split; [exact Hsp|];
  split; [exact Hb|]; split; [exact Hr|]; split; [exact Hz|]; intros i Hi; exact (IH _ _ _ (Hc i Hi))).
  destruct Hx as (z & Hz & Hc). exists z. split; [exact (Ha _ Hz)|]. exact (IH _ _ _ Hc).
- exact H.
- exact I.
Qed.

Lemma tsim_bind : forall {A B} (R : A -> A -> Prop) (R' : B -> B -> Prop) t0 t1 k0 k1,
  tsim R t0 t1 -> (forall r0 r1, R r0 r1 -> tsim R' (k0 r0) (k1 r1)) -> tsim R' (ibind t0 k0) (ibind t1 k1).
Proof.
intros A B R R' t0 t1 k0 k1 H Hk.
induction H as [r0 r1 Hr | q s0 s1 c0 c1 Ha Hc IH | pc | f tx]; cbn [ibind].
- exact (Hk r0 r1 Hr).
- apply tsim_ask; [exact Ha | intros z; exact (IH z)].
- apply tsim_spin.
- apply tsim_fail.
Qed.

(* A monadic step [m] commutes with the shift: from s and from exh_set c s it builds trees related by
   [exh_rel c], the result of the shifted run being the shift of the result of the plain run. *)
Definition exh_rel {A : Type} (c : Z) (r0 r1 : A * astate) : Prop := r1 = (fst r0, exh_set c (snd r0)).
Definition exh_shifts {A : Type} (c : Z) (m : M A) : Prop := forall s, tsim (exh_rel c) (m s) (m (exh_set c s)).

Lemma rep_shifts_ret : forall {A} c (a : A), exh_shifts c (ret a).
Proof. intros A c a s. unfold ret. apply tsim_ret. unfold exh_rel. reflexivity. Qed.

Lemma rep_shifts_spin : forall {A} c pc, exh_shifts c (@spin A pc).
Proof. intros A c pc s. unfold spin. apply tsim_spin. Qed.

Lemma rep_shifts_bind : forall {A B} c (m : M A) (k : A -> M B),
  exh_shifts c m -> (forall a, exh_shifts c (k a)) -> exh_shifts c (bind m k).
Proof.
intros A B c m k Hm Hk s. unfold bind.
apply (tsim_bind (exh_rel c)); [exact (Hm s) |].
intros r0 r1 Hr. unfold exh_rel in Hr. subst r1. destruct r0 as [a s0]. exact (Hk a s0).
Qed.

Lemma rep_shifts_get : forall {B} c (k : astate -> M B),
  (forall s s', k (exh_set c s) s' = k s s') -> (forall s0, exh_shifts c (k s0)) -> exh_shifts c (bind get k).
Proof. intros B c k Hk Hs s. unfold bind, get. cbn [ibind]. rewrite Hk. exact (Hs s s). Qed.

Lemma rep_shifts_modify : forall c (g : astate -> astate),
  (forall s, g (exh_set c s) = exh_set c (g s)) -> exh_shifts c (modify g).
Proof. intros c g Hg s. unfold modify. rewrite Hg. apply tsim_ret. unfold exh_rel. reflexivity. Qed.

Lemma rep_shifts_askz_mmap : forall c n, exh_shifts c (askz (KMmapSec n)).
Proof.
intros c n s. unfold askz. apply tsim_ask.
- intros z H. exact H.
- intros z. apply tsim_ret. unfold exh_rel. reflexivity.
Qed.

Lemma rep_shifts_tick : forall c, exh_shifts c tick.
Proof. intros c. unfold tick. apply rep_shifts_modify. intros s. destruct s. reflexivity. Qed.

Lemma rep_shifts_retire : forall c, exh_shifts c errb_retire.
Proof. intros c. unfold errb_retire. apply rep_shifts_modify. intros s. destruct s. reflexivity. Qed.

Lemma rep_shifts_set_size : forall c ns, exh_shifts c (errb_set_size ns).
Proof.
intros c ns. unfold errb_set_size. apply rep_shifts_modify. intros s. cbv beta.
rewrite rep_exh_secs. destruct (find_sz (st_secs s) 0%nat); apply rep_exh_set_secs.
Qed.

Lemma rep_shifts_map : forall c want, exh_shifts c (errb_map_cf want).
Proof.
intros c want. unfold errb_map_cf. cbv zeta.
apply rep_shifts_bind; [apply rep_shifts_tick | intros u; cbv beta].
apply rep_shifts_bind; [apply rep_shifts_askz_mmap | intros z; cbv beta].
destruct (z =? 0); [apply rep_shifts_spin |].
apply rep_shifts_bind; [apply rep_shifts_retire | intros u'; cbv beta].
apply rep_shifts_modify. intros s. destruct s. reflexivity.
Qed.

Lemma rep_shifts_append : forall c l, exh_shifts c (errb_append_cf l).
Proof.
intros c l. unfold errb_append_cf. apply rep_shifts_get.
- intros s s'. cbv beta. rewrite rep_exh_mapped, rep_exh_size, rep_exh_cap. reflexivity.
- intros s0. cbv beta. destruct (negb (errb_mapped_cf s0)).
  + apply rep_shifts_bind; [apply rep_shifts_map | intros u; cbv beta].
    apply rep_shifts_get.
    * intros s s'. cbv beta. rewrite rep_exh_cap. reflexivity.
    * intros s1. cbv beta. apply rep_shifts_bind; [| intros u'; cbv beta; apply rep_shifts_set_size].
      destruct (errb_cap_cf s1 <? l); [apply rep_shifts_map | apply rep_shifts_ret].
  + cbv zeta. apply rep_shifts_bind; [| intros u; cbv beta; apply rep_shifts_set_size].
    destruct (errb_cap_cf s0 <? errb_size_cf s0 + l); [apply rep_shifts_map | apply rep_shifts_ret].
Qed.

Lemma tsim_append_exh : forall c l s,
  tsim (fun r0 r1 => r1 = (fst r0, exh_set c (snd r0))) (errb_append_cf l s) (errb_append_cf l (exh_set c s)).
Proof. intros c l s. exact (rep_shifts_append c l s). Qed.

(* ---------------------------------------------------------------------------- *)
(* (3) The class-full reduction and the bridge.                                  *)
Lemma rep_ibind_assoc : forall {St A B C : Type} (t : itree St A) (k : A -> itree St B) (k' : B -> itree St C),
  ibind (ibind t k) k' = ibind t (fun a => ibind (k a) k').
Proof.
intros St A B C t. induction t as [a | q s c0 IH | pc | f]; intros k k'; cbn [ibind]; try reflexivity.
f_equal. apply functional_extensionality. intros z. apply IH.
Qed.

Lemma rep_round_up_user : forall x, 0 < x <= kUserMapSize -> round_up x kUserMapSize = kUserMapSize.
Proof.
intros x Hx. unfold round_up.
replace (x + kUserMapSize - 1) with (x - 1 + 1 * kUserMapSize) by lia.
rewrite Z.div_add by (unfold kUserMapSize; lia).
rewrite (Z.div_small (x - 1) kUserMapSize) by (unfold kUserMapSize in *; lia).
lia.
Qed.

Lemma rep_bind_get : forall {A} (k : astate -> M A) s, bind get k s = k s s.
Proof. intros A k s. reflexivity. Qed.

Lemma rep_bind_get_region : forall {A} c (k : region -> M A) s, bind (get_region c) k s = k (reg s c) s.
Proof. intros A c k s. reflexivity. Qed.

Lemma rep_bind_get_pc : forall {A} c (k : pclass -> M A) s, bind (get_pc c) k s = k (cache s c) s.
Proof. intros A c k s. reflexivity. Qed.

Lemma rep_bind_ret : forall {A B} (m : M A) (k : A -> M B) s a s', m s = IRet (a, s') -> bind m k s = k a s'.
Proof. intros A B m k s a s' H. unfold bind. rewrite H. reflexivity. Qed.

Lemma rep_init_eq : forall S, st_cache_inited S = true -> init_cache_if_needed S = IRet (tt, S).
Proof. intros S H. unfold init_cache_if_needed. rewrite rep_bind_get. cbv beta. rewrite H. reflexivity. Qed.

(* The two report appends from S, then the shift, with result a. *)
Definition rep_tree {A : Type} (S : astate) (c : Z) (a : A) : itree astate (A * astate) :=
  ibind (errb_append_cf exh_len1 S)
        (fun r1 => ibind (errb_append_cf (exh_len2 c) (snd r1)) (fun r2 => IRet (a, exh_set c (snd r2)))).

(* A continuation that, on the result a, only rewrites the result keeps the tree's shape. *)
Lemma rep_bind_rep : forall {A B} (m : M A) (k : A -> M B) s S c (a : A) (b : B),
  m s = rep_tree S c a -> (forall s', k a s' = IRet (b, s')) -> bind m k s = rep_tree S c b.
Proof.
intros A B m k s S c a b Hm Hk. unfold bind. rewrite Hm. unfold rep_tree. rewrite rep_ibind_assoc.
f_equal. apply functional_extensionality. intros r1. cbv beta. rewrite rep_ibind_assoc.
f_equal. apply functional_extensionality. intros r2. cbv beta. cbn [ibind]. apply Hk.
Qed.

(* map_more_user_cf's class-full arm (YG00cf.v:177) on a class whose byte is clear. *)
Lemma rep_arm : forall c S, exh_mem_cf S c = false ->
  (errb_report_cf c ;; set_exh_cf c ;; ret false) S = rep_tree S c false.
Proof.
intros c S Hexh.
assert (Hr : errb_report_cf c S = ibind (errb_append_cf exh_len1 S) (fun r1 => errb_append_cf (exh_len2 c) (snd r1))).
{ unfold errb_report_cf. rewrite rep_bind_get. cbv beta. rewrite Hexh. cbv iota. unfold bind.
  f_equal. apply functional_extensionality. intros [u s1]. reflexivity. }
unfold bind. rewrite Hr. rewrite rep_ibind_assoc. unfold rep_tree.
f_equal. apply functional_extensionality. intros r1. cbv beta.
f_equal. apply functional_extensionality. intros [u2 s2]. cbv beta iota.
rewrite set_exh_cf_eq. reflexivity.
Qed.

Lemma tree_classfull_cf : forall (c n need : Z) (S : astate),
  1 <= c <= 31 -> c <> kBatchClass ->
  st_cache_inited S = true -> pc_chunks (cache S c) = [] -> pc_max (cache S c) = max_cached c ->
  n = max_cached c / 2 -> fa_len (rg_free (reg S c)) < n -> need = n - fa_len (rg_free (reg S c)) ->
  rg_mapped_user (reg S c) < rg_alloc_user (reg S c) + need * class_size c ->
  0 < rg_alloc_user (reg S c) + need * class_size c - rg_mapped_user (reg S c) <= kUserMapSize ->
  kFreeArrayOffset < rg_mapped_user (reg S c) + kUserMapSize ->
  exh_mem_cf S c = false ->
  refill_tree_cf c S =
  ibind (errb_append_cf exh_len1 S)
        (fun r1 => ibind (errb_append_cf (exh_len2 c) (snd r1)) (fun r2 => IRet (tt, exh_set c (snd r2)))).
Proof.
intros c n need S Hc Hb Hinit Hch Hmax Hn Hlt Hneed Hmu Hrange Hfo Hexh.
assert (HB : (c =? kBatchClass) = false) by (apply Z.eqb_neq; exact Hb).
assert (Hmm : map_more_user_cf c need S = rep_tree S c false).
{ unfold map_more_user_cf. rewrite HB. cbv beta iota zeta.
  rewrite rep_bind_get_region. cbv beta.
  rewrite (proj2 (Z.ltb_lt _ _) Hmu). cbv iota.
  rewrite (rep_round_up_user _ Hrange).
  rewrite (proj2 (Z.leb_gt _ _) Hfo). cbv iota.
  exact (rep_arm c S Hexh). }
assert (Hpop : populate_cf c need S = rep_tree S c false).
{ unfold populate_cf. rewrite HB. cbv iota.
  eapply rep_bind_rep; [exact Hmm | intros s'; reflexivity]. }
assert (Hgfa : get_from_allocator_cf c n S = rep_tree S c (@None (list Z))).
{ unfold get_from_allocator_cf. rewrite rep_bind_get_region. cbv beta.
  rewrite (proj2 (Z.ltb_lt _ _) Hlt). cbv iota. rewrite <- Hneed.
  eapply rep_bind_rep; [exact Hpop | intros s'; reflexivity]. }
assert (Hrie : refill_if_empty_cf c S = rep_tree S c tt).
{ unfold refill_if_empty_cf. rewrite rep_bind_get_pc. cbv beta. rewrite Hch. cbv iota.
  rewrite Hmax, <- Hn. eapply rep_bind_rep; [exact Hgfa | intros s'; reflexivity]. }
unfold refill_tree_cf. rewrite (rep_bind_ret _ _ _ _ _ (rep_init_eq S Hinit)). exact Hrie.
Qed.

Lemma amreal_classfull_shift : forall segs c S W cfg Q,
  amreal segs (ibind (errb_append_cf exh_len1 (exh_set c S))
                 (fun r1 => ibind (errb_append_cf (exh_len2 c) (snd r1)) (fun r2 => IRet (tt, snd r2)))) W cfg Q ->
  amreal segs (ibind (errb_append_cf exh_len1 S)
                 (fun r1 => ibind (errb_append_cf (exh_len2 c) (snd r1)) (fun r2 => IRet (tt, exh_set c (snd r2))))) W cfg Q.
Proof.
intros segs c S W cfg Q H.
refine (amreal_tsim segs eq _ _ W cfg Q Q _ _ H).
- apply (tsim_bind (exh_rel c)); [exact (rep_shifts_append c exh_len1 S) |].
  intros r0 r1 Hr. unfold exh_rel in Hr. subst r1. cbn [snd].
  apply (tsim_bind (exh_rel c)); [exact (rep_shifts_append c (exh_len2 c) (snd r0)) |].
  intros q0 q1 Hq. unfold exh_rel in Hq. subst q1. cbn [snd]. apply tsim_ret. reflexivity.
- intros r0 r1 W' c' Hr HQ. subst r1. exact HQ.
Qed.

(* ---------------------------------------------------------------------------- *)
(* (4) The other arm: the class's byte is ALREADY set (exh_mem_cf S c = true).    *)
(* errb_report_cf prints nothing (YG00cf.v:149) and set_exh_cf finds its hole in  *)
(* place, so the whole tree returns (tt, S): a class's holes are only the one     *)
(* sentinel and NoDup (wrc_holes, YG01cf.v:43), so add_hole re-makes the same list.*)
Lemma rep_arm_set : forall c S, exh_mem_cf S c = true ->
  (errb_report_cf c ;; set_exh_cf c ;; ret false) S = IRet (false, exh_set c S).
Proof.
intros c S Hexh.
assert (Hr : errb_report_cf c S = IRet (tt, S)).
{ unfold errb_report_cf. rewrite rep_bind_get. cbv beta. rewrite Hexh. reflexivity. }
rewrite (rep_bind_ret _ _ _ _ _ Hr). cbv beta.
rewrite (rep_bind_ret _ _ _ _ _ (set_exh_cf_eq c S)). reflexivity.
Qed.

Lemma tree_classfull_set_cf : forall (c n need : Z) (S : astate),
  c <> kBatchClass ->
  st_cache_inited S = true -> pc_chunks (cache S c) = [] -> pc_max (cache S c) = max_cached c ->
  n = max_cached c / 2 -> fa_len (rg_free (reg S c)) < n -> need = n - fa_len (rg_free (reg S c)) ->
  rg_mapped_user (reg S c) < rg_alloc_user (reg S c) + need * class_size c ->
  0 < rg_alloc_user (reg S c) + need * class_size c - rg_mapped_user (reg S c) <= kUserMapSize ->
  kFreeArrayOffset < rg_mapped_user (reg S c) + kUserMapSize ->
  exh_mem_cf S c = true ->
  refill_tree_cf c S = IRet (tt, exh_set c S).
Proof.
intros c n need S Hb Hinit Hch Hmax Hn Hlt Hneed Hmu Hrange Hfo Hexh.
assert (HB : (c =? kBatchClass) = false) by (apply Z.eqb_neq; exact Hb).
assert (Hmm : map_more_user_cf c need S = IRet (false, exh_set c S)).
{ unfold map_more_user_cf. rewrite HB. cbv beta iota zeta.
  rewrite rep_bind_get_region. cbv beta.
  rewrite (proj2 (Z.ltb_lt _ _) Hmu). cbv iota.
  rewrite (rep_round_up_user _ Hrange).
  rewrite (proj2 (Z.leb_gt _ _) Hfo). cbv iota.
  exact (rep_arm_set c S Hexh). }
assert (Hpop : populate_cf c need S = IRet (false, exh_set c S)).
{ unfold populate_cf. rewrite HB. cbv iota. rewrite (rep_bind_ret _ _ _ _ _ Hmm). reflexivity. }
assert (Hgfa : get_from_allocator_cf c n S = IRet (@None (list Z), exh_set c S)).
{ unfold get_from_allocator_cf. rewrite rep_bind_get_region. cbv beta.
  rewrite (proj2 (Z.ltb_lt _ _) Hlt). cbv iota. rewrite <- Hneed.
  rewrite (rep_bind_ret _ _ _ _ _ Hpop). reflexivity. }
assert (Hrie : refill_if_empty_cf c S = IRet (tt, exh_set c S)).
{ unfold refill_if_empty_cf. rewrite rep_bind_get_pc. cbv beta. rewrite Hch. cbv iota.
  rewrite Hmax, <- Hn. rewrite (rep_bind_ret _ _ _ _ _ Hgfa). reflexivity. }
unfold refill_tree_cf. rewrite (rep_bind_ret _ _ _ _ _ (rep_init_eq S Hinit)). exact Hrie.
Qed.

(* The shift is the identity on a class whose sentinel is already there. *)
Lemma exh_set_same : forall c S, 0 <= c -> (Z.to_nat c < length (st_regions S))%nat ->
  Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes (reg S c)) -> NoDup (rg_holes (reg S c)) ->
  exh_mem_cf S c = true -> exh_set c S = S.
Proof.
intros c S Hc Hl Hf Hnd Hexh.
assert (Hh : rg_holes (reg S c) = [(EXH_HOLE, 0)]).
{ unfold exh_mem_cf in Hexh. revert Hf Hnd Hexh. generalize (rg_holes (reg S c)) as l.
  intros [|h [|h2 t]] Hf Hnd Hexh; [discriminate Hexh | |].
  - inversion Hf; subst; reflexivity.
  - exfalso. inversion Hf as [|? ? E1 F1]; subst. inversion F1 as [|? ? E2 _]; subst.
    inversion Hnd as [|? ? Hnin _]; subst; apply Hnin; left; reflexivity. }
unfold exh_set. cbv zeta. rewrite Hh.
replace (add_hole (EXH_HOLE, 0) [(EXH_HOLE, 0)]) with [(EXH_HOLE, 0)] by (unfold add_hole; reflexivity).
rewrite <- Hh. destruct (reg S c) as [mu0 au0 mf0 fr0 ho0] eqn:ER.
cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes].
rewrite <- ER. apply upd_reg_same; assumption.
Qed.

End a.
