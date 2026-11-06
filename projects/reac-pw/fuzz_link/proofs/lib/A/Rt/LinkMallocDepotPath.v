(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfAmx.v, with its module paths changed; 81 of its 146 lines of code are new or changed and 189 lines of the source are left out. *)
(* THE DEPOT ACROSS ONE MALLOC OR FREE of the allocator model (lib/Reusable/YG00.v malloc, free), on a returning model
   path:
     ds_malloc         : ipost (malloc n tr s) (fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr])
     malloc_depot_path : apath (malloc n tr s) trc r -> st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr]
     ds_free           : ipost (free p tr s) (fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr])
     free_depot_path   : apath (free p tr s) trc r -> st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr].
   malloc puts its trace with one depot_put (YG00.v:427) on its success path, free with one (YG00.v:558) on its live-block
   arm; their callees (cache_alloc, sec_alloc, enqueue, maybe_drain and theirs) keep the depot. Image-free, no
   invariant: an all-paths post (ipost) on every returning path of the model, turned into a statement about apath
   (ds_ipost_apath). lib/A/Rt/LinkMallocDepot.v uses malloc_depot_path and free_depot_path.
   A port of omx-clap-core/fuzz_preset lib/Reusable/YGcfDepotStep.v (hub 26d8d53a1503), first allocator only:
   ds_ipost_apath (:30), ds_cbn / ds_unf / ds_step (:50-73), ds_gfa (:75), ds_refill (:79), ds_calloc (:83), and the
   free-path posts ds_enqueue (:87), ds_rta (:91), ds_cdealloc (:95), ds_sdealloc (:99), ds_rchunk (:103),
   ds_ritems (:107), ds_drecycle (:114); with the pieces of YGcfAmx.v (same tree) they need: ipost, ipost_mono,
   ipost_ibind, ipost_ibind_assoc (:35-70) and the depot posts dep_ensure (:233), dep_mmu (:237), dep_populate (:241),
   dep_sec_alloc (:245), dep_depot_put (:249), here proved with ds_step (YGcfAmx.v's dep_step unfolds names of the
   second allocator). ds_malloc follows YGcfAmx.v's dep_malloc_cf (:286) and malloc_depot_path its dep_malloc_cf_apath
   (:302); ds_drain and ds_free are YGcfDepotStep.v's ds_drain_cf (:120) and ds_free_cf (:125) at the first
   allocator's maybe_drain (YG00.v:534) and free (YG00.v:546), and free_depot_path is malloc_depot_path's form.
   Nothing of the second allocator.
   rule 24: proves no function (kind: kit lemma, the allocator model's depot across one malloc or free). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. All-paths posts. ipost t P: every IRet of t satisfies P. It asks nothing of *)
(*    the requests, so it holds without any invariant.                            *)
Fixpoint ipost {A : Type} (t : itree astate A) (P : A -> Prop) : Prop :=
match t with
| IRet a => P a
| IAsk _ _ k => forall z, ipost (k z) P
| ISpin _ => True
| IFail _ => True
end.

Lemma ipost_mono {A} (t : itree astate A) : forall (P Q : A -> Prop), (forall a, P a -> Q a) -> ipost t P -> ipost t Q.
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [ipost]; intros P Q HPQ H.
- exact (HPQ a H).
- intros z. exact (IH z P Q HPQ (H z)).
- exact I.
- exact I.
Qed.

Lemma ipost_ibind {A B} (t : itree astate A) : forall (k : A -> itree astate B) (P : B -> Prop),
ipost t (fun a => ipost (k a) P) -> ipost (ibind t k) P.
Proof.
induction t as [a | q sn c IH | pc | f]; cbn [ibind ipost]; intros k P H.
- exact H.
- intros z. apply IH. exact (H z).
- exact I.
- exact I.
Qed.

Lemma ipost_ibind_assoc {A B C} (t : itree astate A) : forall (k1 : A -> itree astate B) (k2 : B -> itree astate C) P,
ipost (ibind t (fun a => ibind (k1 a) k2)) P -> ipost (ibind (ibind t k1) k2) P.
Proof.
induction t as [a | q sn c IH | pc | f]; cbn [ibind ipost]; intros k1 k2 P H.
- exact H.
- intros z. apply IH. exact (H z).
- exact I.
- exact I.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. A returning path satisfies every all-paths post.                            *)
Lemma ds_ipost_apath : forall {A} (t : itree astate A) (P : A -> Prop) tr a, ipost t P -> apath t tr a -> P a.
Proof.
intros A t P. induction t as [a' | q sn k IH | pc | f]; intros tr a H Hp.
- destruct tr; cbn [apath] in Hp; [subst a'; exact H | destruct Hp].
- destruct tr as [|[q' z] tr']; cbn [apath] in Hp; [destruct Hp|]. destruct Hp as (_ & _ & Hp).
  exact (IH z tr' a (H z) Hp).
- destruct tr; cbn [apath] in Hp; destruct Hp.
- destruct tr; cbn [apath] in Hp; destruct Hp.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The depot is kept by malloc's callees (YG00.v) and grows by the call's      *)
(*    trace at most once, in depot_put. One step of an all-paths depot post:      *)
(*    unfold the monad's primitives, compute, split on a condition, or use a      *)
(*    proved post of a callee (hint database dsdb).                               *)
Create HintDb dsdb.

Ltac ds_cbn :=
cbn [ibind ipost fst snd st_depot set_regions set_cache set_chunks set_secs set_sec_arr set_sec_reserved set_depot
set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac ds_unf :=
progress (unfold get_region, set_region, get_pc, set_pc, init_cache_if_needed, tick, bind, get, put, modify, askz,
ret, mcheck, fail, spin in *).

Ltac ds_step :=
first
[ progress ds_cbn
| ds_unf
| progress intros
| match goal with |- ipost (ibind (ibind _ _) _) _ => apply ipost_ibind_assoc end
| match goal with |- ipost (ibind _ _) _ =>
apply ipost_ibind; eapply ipost_mono; [|solve [eauto with dsdb]];
let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hd" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- ipost _ _ =>
eapply ipost_mono; [|solve [eauto with dsdb]];
let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hd" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| match goal with H : _ \/ _ |- _ => destruct H end
| solve [reflexivity | congruence | left; congruence | right; congruence] ].

Lemma dep_ensure : forall c need sof s, ipost (ensure_free_array c need sof s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need sof s. unfold ensure_free_array. repeat ds_step. Qed.
#[local] Hint Resolve dep_ensure : dsdb.

Lemma dep_mmu : forall c need s, ipost (map_more_user c need s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need s. unfold map_more_user. repeat ds_step. Qed.
#[local] Hint Resolve dep_mmu : dsdb.

Lemma dep_populate : forall c need s, ipost (populate c need s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need s. unfold populate. repeat ds_step. Qed.
#[local] Hint Resolve dep_populate : dsdb.

Lemma dep_sec_alloc : forall n s, ipost (sec_alloc n s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros n s. unfold sec_alloc. repeat ds_step. Qed.
#[local] Hint Resolve dep_sec_alloc : dsdb.

Lemma dep_depot_put : forall tr s, ipost (depot_put tr s)
(fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr]).
Proof. intros tr s. unfold depot_put. repeat ds_step. Qed.
#[local] Hint Resolve dep_depot_put : dsdb.

Lemma ds_gfa : forall c n s, ipost (get_from_allocator c n s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c n s. unfold get_from_allocator. repeat ds_step. Qed.
#[local] Hint Resolve ds_gfa : dsdb.

Lemma ds_refill : forall c s, ipost (refill_if_empty c s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c s. unfold refill_if_empty. repeat ds_step. Qed.
#[local] Hint Resolve ds_refill : dsdb.

Lemma ds_calloc : forall c s, ipost (cache_alloc c s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c s. unfold cache_alloc. repeat ds_step. Qed.
#[local] Hint Resolve ds_calloc : dsdb.

Lemma ds_enqueue : forall k s, ipost (enqueue k s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros k s. unfold enqueue. repeat ds_step. Qed.
#[local] Hint Resolve ds_enqueue : dsdb.

Lemma ds_rta : forall c offs s, ipost (return_to_allocator c offs s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c offs s. unfold return_to_allocator. repeat ds_step. Qed.
#[local] Hint Resolve ds_rta : dsdb.

Lemma ds_cdealloc : forall c off s, ipost (cache_dealloc c off s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c off s. unfold cache_dealloc. repeat ds_step. Qed.
#[local] Hint Resolve ds_cdealloc : dsdb.

Lemma ds_sdealloc : forall r s, ipost (sec_dealloc r s) (fun x => st_depot (snd x) = st_depot s).
Proof. intros r s. unfold sec_dealloc. repeat ds_step. Qed.
#[local] Hint Resolve ds_sdealloc : dsdb.

Lemma ds_rchunk : forall k s, ipost (recycle_chunk k s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros k s. unfold recycle_chunk. repeat ds_step. Qed.
#[local] Hint Resolve ds_rchunk : dsdb.

Lemma ds_ritems : forall fuel items s, ipost (recycle_items fuel items s) (fun r => st_depot (snd r) = st_depot s).
Proof.
(* the recursive call is solved by IH, which eauto takes from the context *)
induction fuel as [|f IH]; intros [|k t] s; cbn [recycle_items]; repeat ds_step.
Qed.
#[local] Hint Resolve ds_ritems : dsdb.

Lemma ds_drecycle : forall fuel bs s, ipost (do_recycle fuel bs s) (fun r => st_depot (snd r) = st_depot s).
Proof.
induction fuel as [|f IH]; intros [|b t] s; cbn [do_recycle]; repeat ds_step.
Qed.
#[local] Hint Resolve ds_drecycle : dsdb.

Lemma ds_drain : forall s, ipost (maybe_drain s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros s. unfold maybe_drain. repeat ds_step. Qed.
#[local] Hint Resolve ds_drain : dsdb.

(* malloc: the depot is kept, or the call's trace is appended once (its depot_put). *)
Theorem ds_malloc : forall n tr s, ipost (malloc n tr s)
(fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr]).
Proof. intros n tr s. unfold malloc. repeat ds_step. Qed.

(* free: the depot is kept, or the call's trace is appended once (its depot_put). *)
Theorem ds_free : forall p tr s, ipost (free p tr s)
(fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr]).
Proof. intros p tr s. unfold free. repeat ds_step. Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. THE DEPOT ACROSS ONE MALLOC OR FREE, on a returning model path.             *)
Theorem malloc_depot_path : forall n tr s trc r, apath (malloc n tr s) trc r ->
st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr].
Proof. intros n tr s trc r H. exact (ds_ipost_apath _ _ _ _ (ds_malloc n tr s) H). Qed.

Theorem free_depot_path : forall p tr s trc r, apath (free p tr s) trc r ->
st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr].
Proof. intros p tr s trc r H. exact (ds_ipost_apath _ _ _ _ (ds_free p tr s) H). Qed.

About ds_malloc.
Print Assumptions ds_malloc.
About malloc_depot_path.
Print Assumptions malloc_depot_path.
About ds_free.
Print Assumptions ds_free.
About free_depot_path.
Print Assumptions free_depot_path.
