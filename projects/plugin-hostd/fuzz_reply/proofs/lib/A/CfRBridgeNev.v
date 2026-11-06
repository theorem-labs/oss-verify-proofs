(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: plugin-hostd/fuzz_reply.asan, the cf allocator bridge (a Theorem Labs lane R, new file), part 3:
   the TICK UPDATE of a malloc_cf that returns a block (EXCEPTION 3 of the event-term gate, Main 2026-10-30 00:2xZ:
   the journal's st_nev conjunct, YCbqG.v:249, grows by the call's own model ticks). malloc_cf (YG00cf.v) ticks once
   at its entry; the only other ticks are errb_map_cf's (YG00cf.v), which run only inside the class-full report of
   map_more_user_cf, an arm that returns false, so populate_cf, get_from_allocator_cf and cache_alloc_cf then fail
   and malloc_cf returns PNull. So every return of malloc_cf with a block has st_nev = the entry's + 1
   (malloc_cf_block_nev). malloc_post_cf (YG07cf.v:259) gives only the lower bound.
   Proved over YGcfXs.cfx_ipost (every return of the tree), by the fr_* walk of YGcfXs.v (:440-470) restated with two
   predicates: the tick count, and the cache (unchanged by a failed refill). Model lemmas only; no function is proved
   (rule 24); no address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require ReallocP.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope am_scope.

Lemma cfx_ipost_any {A : Type} : forall (t : itree astate A) (P : A -> Prop), (forall a, P a) -> cfx_ipost t P.
Proof. induction t as [a | q sn k IH | pc | f]; cbn [cfx_ipost]; intros P H; auto. Qed.

Lemma cfx_ipost_and {A : Type} : forall (t : itree astate A) (P Q : A -> Prop),
  cfx_ipost t P -> cfx_ipost t Q -> cfx_ipost t (fun a => P a /\ Q a).
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [cfx_ipost]; intros P Q H1 H2; auto.
all: intros z; exact (IH z P Q (H1 z) (H2 z)).
Qed.

Definition nev_same (s s' : astate) : Prop := st_nev s' = st_nev s.
Definition nc_same (s s' : astate) : Prop := st_cache s' = st_cache s.

Create HintDb nvdb.
Create HintDb ncdb.

Ltac cr_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed, YG00.tick,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, nev_same, nc_same in *).

Ltac cr_cbn :=
cbn [negb ibind cfx_ipost fst snd st_secs st_chunks st_regions st_cache st_cache_inited st_sec_arr st_sec_reserved st_qthread
st_qglobal st_fs st_depot st_internal_inited st_nev set_regions set_cache set_chunks set_secs set_sec_arr
set_sec_reserved set_depot set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac cr_hint db :=
first
[ match goal with |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind; eapply cfx_ipost_mono; [|solve [eauto with db]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in
  intros [x sx] H1; cbn [fst snd] in H1 end
| match goal with |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono; [|solve [eauto with db]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in
  intros [x sx] H1; cbn [fst snd] in H1 end ].

Ltac cr_step db :=
first
[ progress cr_cbn
| cr_unf
| progress intros
| match goal with H : ?a = ?a -> _ |- _ => specialize (H eq_refl) end
| match goal with H : Some _ <> None -> _ |- _ => specialize (H ltac:(discriminate)) end
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| cr_hint db
| match goal with |- context [negb ?x] => is_var x; destruct x end
| match goal with H : ?x <> None -> _ |- _ => is_var x; destruct x end
| match goal with H : ?x = true -> _ |- _ => is_var x; destruct x end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| congruence ].

Section N. Context {ci : CfImg}.

(* ---------------------------------------------------------------------------- *)
(* 1. The cache: every callee of get_from_allocator_cf leaves st_cache alone.     *)
Lemma nc_ensure : forall c need sof s, cfx_ipost (ensure_free_array c need sof s) (fun r => nc_same s (snd r)).
Proof. intros c need sof s. unfold ensure_free_array. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_ensure : ncdb.
Lemma nc_mmu : forall c need s, cfx_ipost (map_more_user c need s) (fun r => nc_same s (snd r)).
Proof. intros c need s. unfold map_more_user. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_mmu : ncdb.
Lemma nc_populate : forall c need s, cfx_ipost (populate c need s) (fun r => nc_same s (snd r)).
Proof. intros c need s. unfold populate. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_populate : ncdb.
Lemma nc_set_exh : forall c s, cfx_ipost (set_exh_cf c s) (fun r => nc_same s (snd r)).
Proof. intros c s. unfold set_exh_cf. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_set_exh : ncdb.
Lemma nc_clear_exh : forall c s, cfx_ipost (clear_exh_cf c s) (fun r => nc_same s (snd r)).
Proof. intros c s. unfold clear_exh_cf. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_clear_exh : ncdb.
Lemma nc_errb_set_size : forall ns s, cfx_ipost (errb_set_size ns s) (fun r => nc_same s (snd r)).
Proof. intros ns s. unfold errb_set_size. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_errb_set_size : ncdb.
Lemma nc_errb_retire : forall s, cfx_ipost (errb_retire s) (fun r => nc_same s (snd r)).
Proof. intros s. unfold errb_retire. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_errb_retire : ncdb.
Lemma nc_errb_map : forall w s, cfx_ipost (errb_map_cf w s) (fun r => nc_same s (snd r)).
Proof. intros w s. unfold errb_map_cf. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_errb_map : ncdb.
Lemma nc_errb_append : forall len s, cfx_ipost (errb_append_cf len s) (fun r => nc_same s (snd r)).
Proof. intros len s. unfold errb_append_cf. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_errb_append : ncdb.
Lemma nc_errb_report : forall c s, cfx_ipost (errb_report_cf c s) (fun r => nc_same s (snd r)).
Proof. intros c s. unfold errb_report_cf. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_errb_report : ncdb.
Lemma nc_mmu_cf : forall c need s, cfx_ipost (map_more_user_cf c need s) (fun r => nc_same s (snd r)).
Proof. intros c need s. unfold map_more_user_cf. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_mmu_cf : ncdb.
Lemma nc_populate_cf : forall c need s, cfx_ipost (populate_cf c need s) (fun r => nc_same s (snd r)).
Proof. intros c need s. unfold populate_cf. repeat cr_step ncdb. Qed.
#[local] Hint Resolve nc_populate_cf : ncdb.
Lemma nc_gfa_cf : forall c n s, cfx_ipost (get_from_allocator_cf c n s) (fun r => nc_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator_cf. repeat cr_step ncdb. Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The ticks: the callees that never tick.                                      *)
Lemma nv_ensure : forall c need sof s, cfx_ipost (ensure_free_array c need sof s) (fun r => nev_same s (snd r)).
Proof. intros c need sof s. unfold ensure_free_array. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_ensure : nvdb.
Lemma nv_mmu : forall c need s, cfx_ipost (map_more_user c need s) (fun r => nev_same s (snd r)).
Proof. intros c need s. unfold map_more_user. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_mmu : nvdb.
Lemma nv_populate : forall c need s, cfx_ipost (populate c need s) (fun r => nev_same s (snd r)).
Proof. intros c need s. unfold populate. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_populate : nvdb.
Lemma nv_set_exh : forall c s, cfx_ipost (set_exh_cf c s) (fun r => nev_same s (snd r)).
Proof. intros c s. unfold set_exh_cf. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_set_exh : nvdb.
Lemma nv_clear_exh : forall c s, cfx_ipost (clear_exh_cf c s) (fun r => nev_same s (snd r)).
Proof. intros c s. unfold clear_exh_cf. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_clear_exh : nvdb.
Lemma nv_sec_alloc : forall n s, cfx_ipost (sec_alloc n s) (fun r => nev_same s (snd r)).
Proof. intros n s. unfold sec_alloc. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_sec_alloc : nvdb.
Lemma nv_depot : forall tr s, cfx_ipost (depot_put tr s) (fun r => nev_same s (snd r)).
Proof. intros tr s. unfold depot_put. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_depot : nvdb.

(* ---------------------------------------------------------------------------- *)
(* 3. The class-full report ticks, but only on a path that returns false / None.   *)
Lemma nv_mmu_cf : forall c need s, cfx_ipost (map_more_user_cf c need s) (fun r => fst r = true -> nev_same s (snd r)).
Proof.
intros c need s. unfold map_more_user_cf. destruct (c =? kBatchClass).
- eapply cfx_ipost_mono; [|apply nv_mmu]. intros [x sx] H _. exact H.
- repeat (first
  [ progress cr_cbn | cr_unf | progress intros
  | match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
  | match goal with |- cfx_ipost (ibind (errb_report_cf _ _) _) _ =>
      apply cfx_ipost_ibind; apply cfx_ipost_any; intros [? ?] end
  | cr_hint nvdb
  | match goal with |- context [match ?x with _ => _ end] => destruct x end
  | exact I | congruence ]).
Qed.
#[local] Hint Resolve nv_mmu_cf : nvdb.

Lemma nv_populate_cf : forall c need s, cfx_ipost (populate_cf c need s) (fun r => fst r = true -> nev_same s (snd r)).
Proof.
intros c need s. unfold populate_cf. destruct (c =? kBatchClass).
- eapply cfx_ipost_mono; [|apply nv_populate]. intros [x sx] H _. exact H.
- repeat cr_step nvdb.
Qed.
#[local] Hint Resolve nv_populate_cf : nvdb.

Lemma nv_gfa_cf : forall c n s, cfx_ipost (get_from_allocator_cf c n s) (fun r => fst r <> None -> nev_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator_cf. repeat cr_step nvdb. Qed.

Lemma nv_refill_cf : forall c s, cfx_ipost (refill_if_empty_cf c s)
  (fun r => st_nev (snd r) = st_nev s \/ pc_chunks (cache (snd r) c) = []).
Proof.
intros c s. unfold refill_if_empty_cf, YG00.get_pc, YG00.bind, YG00.get, YG00.ret. cr_cbn.
destruct (pc_chunks (znth pclass0 c (st_cache s))) as [|z l] eqn:E.
- apply cfx_ipost_ibind.
  eapply cfx_ipost_mono; [|exact (cfx_ipost_and _ _ _ (nv_gfa_cf c (pc_max (znth pclass0 c (st_cache s)) / 2) s)
    (nc_gfa_cf c (pc_max (znth pclass0 c (st_cache s)) / 2) s))].
  intros [got s1] [H1 H2]. cbn [fst snd] in H1, H2. unfold nev_same, nc_same in *. destruct got as [tops|].
  + left. unfold YG00.set_pc, YG00.modify. cr_cbn. apply H1. discriminate.
  + right. cr_cbn. unfold cache. rewrite H2. exact E.
- left. reflexivity.
Qed.

Lemma nv_init_cache : forall s, cfx_ipost (init_cache_if_needed s) (fun r => nev_same s (snd r)).
Proof. intros s. unfold init_cache_if_needed. repeat cr_step nvdb. Qed.

Lemma nv_cache_alloc_cf : forall c s, cfx_ipost (cache_alloc_cf c s) (fun r => fst r <> None -> nev_same s (snd r)).
Proof.
intros c s. unfold cache_alloc_cf.
assert (K : forall s0, st_nev s0 = st_nev s ->
  cfx_ipost (YG00.bind (refill_if_empty_cf c) (fun _ => YG00.bind (YG00.get_pc c) (fun p =>
    match pc_chunks p with [] => YG00.ret None | l => YG00.bind (YG00.set_pc c (mkPC (pc_max p) (removelast l)))
    (fun _ => YG00.ret (Some (region_off c + last l 0))) end)) s0) (fun r => fst r <> None -> nev_same s (snd r))).
{ intros s0 E0. unfold YG00.bind at 1. apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|apply nv_refill_cf].
  intros [u s1] H1. cbn [fst snd] in H1. unfold YG00.get_pc, YG00.bind, YG00.get, YG00.ret. cr_cbn.
  destruct (pc_chunks (znth pclass0 c (st_cache s1))) as [|z l] eqn:E.
  - cr_cbn. intros H. exfalso. apply H. reflexivity.
  - unfold YG00.set_pc, YG00.modify. cr_cbn. intros _. unfold nev_same. destruct H1 as [H1|H1].
    + cbn in *. congruence.
    + unfold cache in H1. rewrite H1 in E. discriminate E. }
unfold YG00.bind at 1. apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|apply nv_init_cache].
intros [u s0] E0. exact (K s0 E0).
Qed.
#[local] Hint Resolve nv_cache_alloc_cf : nvdb.

(* ---------------------------------------------------------------------------- *)
(* 4. malloc_cf: a block result has exactly one tick.                             *)
Lemma nv_malloc_cf : forall n tr s, cfx_ipost (malloc_cf n tr s) (fun r => fst r <> PNull -> st_nev (snd r) = st_nev s + 1).
Proof. intros n tr s. unfold malloc_cf. repeat cr_step nvdb. Qed.

Theorem malloc_cf_block_nev : forall n tr s trc p s', apath (malloc_cf n tr s) trc (p, s') -> p <> PNull ->
  st_nev s' = st_nev s + 1.
Proof.
intros n tr s trc p s' Hp Hq. exact (cfx_ipost_apath _ _ trc (p, s') (nv_malloc_cf n tr s) Hp Hq).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. free_cf: exactly one tick on every return (its entry's), YGcfXs.v's frame walk (:472-580) over st_nev.     *)
(*    Both of free_cf's arms are covered: enqueue, and recycle_chunk for a chunk above kQuarantineMax.              *)
Lemma nv_gfa : forall c n s, cfx_ipost (get_from_allocator c n s) (fun r => nev_same s (snd r)).
Proof. intros c n s. unfold get_from_allocator. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_gfa : nvdb.
Lemma nv_refill : forall c s, cfx_ipost (refill_if_empty c s) (fun r => nev_same s (snd r)).
Proof. intros c s. unfold refill_if_empty. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_refill : nvdb.
Lemma nv_cache_alloc : forall c s, cfx_ipost (cache_alloc c s) (fun r => nev_same s (snd r)).
Proof. intros c s. unfold cache_alloc. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_cache_alloc : nvdb.
Lemma nv_rta : forall c offs s, cfx_ipost (return_to_allocator c offs s) (fun r => nev_same s (snd r)).
Proof. intros c offs s. unfold return_to_allocator. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_rta : nvdb.
Lemma nv_cache_dealloc : forall c off s, cfx_ipost (cache_dealloc c off s) (fun r => nev_same s (snd r)).
Proof. intros c off s. unfold cache_dealloc. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_cache_dealloc : nvdb.
Lemma nv_enqueue : forall k s, cfx_ipost (enqueue k s) (fun r => nev_same s (snd r)).
Proof. intros k s. unfold enqueue. repeat cr_step nvdb. Qed.
#[local] Hint Resolve nv_enqueue : nvdb.

Definition nev_from (s0 s : astate) : Prop := st_nev s = st_nev s0.

Lemma nev_from_ipost {A : Type} : forall (t : itree astate (A * astate)) s0 s, nev_from s0 s ->
  cfx_ipost t (fun r => nev_same s (snd r)) -> cfx_ipost t (fun r => nev_from s0 (snd r)).
Proof.
intros t s0 s H1 H2. eapply cfx_ipost_mono; [|exact H2]. intros [x sx] E. unfold nev_same, nev_from in *. cbn [snd] in *.
congruence.
Qed.

Lemma nf_sec_dealloc : forall r s0 s, nev_from s0 s -> cfx_ipost (sec_dealloc r s) (fun x => nev_from s0 (snd x)).
Proof.
intros r s0 s H. apply (nev_from_ipost _ s0 s H). unfold sec_dealloc. repeat cr_step nvdb.
Qed.

Lemma nf_recycle_chunk : forall k s0 s, nev_from s0 s -> cfx_ipost (recycle_chunk k s) (fun x => nev_from s0 (snd x)).
Proof.
intros k s0 s H. apply (nev_from_ipost _ s0 s H). unfold recycle_chunk.
repeat (first [progress cr_cbn | cr_unf | progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| match goal with |- cfx_ipost (sec_dealloc _ _) _ =>
    eapply cfx_ipost_mono; [|exact (nf_sec_dealloc _ _ _ eq_refl)]; intros [? ?] Hq; unfold nev_from in Hq; cbn [snd] in Hq end
| cr_hint nvdb
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I | congruence ]).
Qed.

Lemma nf_recycle_items : forall fuel items s0 s, nev_from s0 s -> cfx_ipost (recycle_items fuel items s) (fun x => nev_from s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros items s0 s H; destruct items as [|k t]; cbn [recycle_items]; try cr_unf; try cr_cbn;
try exact H; try exact I.
apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact (nf_recycle_chunk k s0 s H)].
intros [x sx] Hx. cbn [fst snd] in *. apply IH. exact Hx.
Qed.

Lemma nf_do_recycle : forall fuel bs s0 s, nev_from s0 s -> cfx_ipost (do_recycle fuel bs s) (fun x => nev_from s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros bs s0 s H; destruct bs as [|b t]; cbn [do_recycle]; try cr_unf; try cr_cbn;
try exact H; try exact I.
apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact (nf_recycle_items 1100 (b_items b) s0 s H)].
intros [x sx] Hx. cbn [fst snd] in *.
apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|exact (nev_from_ipost _ s0 sx Hx (nv_cache_dealloc kBatchClass (b_self b) sx))].
intros [y sy] Hy. cbn [fst snd] in *. apply IH. exact Hy.
Qed.

Lemma nf_maybe_drain : forall s0 s, nev_from s0 s -> cfx_ipost (maybe_drain_cf s) (fun x => nev_from s0 (snd x)).
Proof.
intros s0 s H. unfold maybe_drain_cf.
repeat (first [progress cr_cbn | cr_unf | progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| match goal with |- cfx_ipost (do_recycle _ _ _) _ => apply nf_do_recycle end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| unfold nev_from in *; cr_cbn; congruence
| assumption]).
Qed.

(* free_cf recycles a chunk above the quarantine's max_size at once (DeallocNmaxA's Quarantine::Put size test). *)
Lemma nv_recycle_chunk : forall k s, cfx_ipost (recycle_chunk k s) (fun r => nev_same s (snd r)).
Proof. intros k s. eapply cfx_ipost_mono; [|exact (nf_recycle_chunk k s s eq_refl)]. intros [x sx] H. exact H. Qed.
#[local] Hint Resolve nv_recycle_chunk : nvdb.

Lemma nv_maybe_drain : forall s, cfx_ipost (maybe_drain_cf s) (fun r => nev_same s (snd r)).
Proof.
intros s. eapply cfx_ipost_mono; [|exact (nf_maybe_drain s s eq_refl)]. intros [x sx] H. exact H.
Qed.
#[local] Hint Resolve nv_maybe_drain : nvdb.

Lemma nv_free_cf : forall p tr s, cfx_ipost (free_cf p tr s) (fun x => st_nev (snd x) = st_nev s + 1).
Proof. intros p tr s. unfold free_cf. repeat cr_step nvdb. Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. The realloc trees: a block result has exactly three ticks (free_cf PNull, malloc_cf, free_cf of the old block); *)
(*    realloc(NULL, n) exactly two.                                                                                 *)
Theorem realloc_tree_nev : forall p n tr s trc q s',
  apath (ReallocP.realloc_tree_with malloc_cf free_cf p n tr s) trc (q, s') -> q <> PNull -> st_nev s' = st_nev s + 3.
Proof.
intros p n tr s trc q s' Hp Hq.
assert (H : cfx_ipost (ReallocP.realloc_tree_with malloc_cf free_cf p n tr s)
  (fun r => fst r <> PNull -> st_nev (snd r) = st_nev s + 3)).
{ unfold ReallocP.realloc_tree_with, YG00.bind at 1. apply cfx_ipost_ibind.
  eapply cfx_ipost_mono; [|apply nv_free_cf]. intros [u s1] E1. cbn [fst snd] in E1.
  unfold YG00.bind at 1. apply cfx_ipost_ibind. eapply cfx_ipost_mono; [|apply nv_malloc_cf].
  intros [q1 s2] E2. cbn [fst snd] in E2. destruct q1 as [| o | r o | c o]; cbn [fst snd];
    [unfold YG00.ret; cbn; intros Hn; exfalso; exact (Hn eq_refl) | .. ].
  all: specialize (E2 ltac:(discriminate)); unfold YG00.bind; apply cfx_ipost_ibind;
       eapply cfx_ipost_mono; [|apply nv_free_cf]; intros [u3 s3] E3; cbn [fst snd] in E3;
       unfold YG00.ret; cbn; intros _; lia. }
exact (cfx_ipost_apath _ _ trc (q, s') H Hp Hq).
Qed.

Theorem realloc_null_tree_nev : forall n tr s trc q s',
  apath (ReallocP.realloc_null_tree_with malloc_cf free_cf n tr s) trc (q, s') -> q <> PNull -> st_nev s' = st_nev s + 2.
Proof.
intros n tr s trc q s' Hp Hq.
assert (H : cfx_ipost (ReallocP.realloc_null_tree_with malloc_cf free_cf n tr s)
  (fun r => fst r <> PNull -> st_nev (snd r) = st_nev s + 2)).
{ unfold ReallocP.realloc_null_tree_with, YG00.bind. apply cfx_ipost_ibind.
  eapply cfx_ipost_mono; [|apply nv_free_cf]. intros [u s1] E1. cbn [fst snd] in *.
  eapply cfx_ipost_mono; [|apply nv_malloc_cf]. intros [q1 s2] E2 Hn. cbn [fst snd] in *. rewrite (E2 Hn). lia. }
exact (cfx_ipost_apath _ _ trc (q, s') H Hp Hq).
Qed.

Theorem free_cf_nev : forall p tr s trc s', apath (free_cf p tr s) trc (tt, s') -> st_nev s' = st_nev s + 1.
Proof. intros p tr s trc s' Hp. exact (cfx_ipost_apath _ _ trc (tt, s') (nv_free_cf p tr s) Hp). Qed.

End N.

Print Assumptions malloc_cf_block_nev.
Print Assumptions free_cf_nev.
Print Assumptions realloc_tree_nev.
Print Assumptions realloc_null_tree_nev.
