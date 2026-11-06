(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfDepotStep.v, with its module paths changed; 2 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30: the DEPOT STEP of the second allocator instance (suffix cf), on a returning model path:
   one malloc_cf or free_cf adds at most its own trace to the depot,
     malloc_cf_depot_step : apath (malloc_cf n tr s) t (p, s') -> incl (st_depot s') (st_depot s ++ [tr])
     free_cf_depot_step   : apath (free_cf p tr s) t (u, s') -> incl (st_depot s') (st_depot s ++ [tr]).
   Image-free, no invariant: an all-paths post (YGcfAmx.v's ipost) on every returning path of the model, turned into
   a statement about apath. malloc_cf's post is YGcfAmx.v's dep_malloc_cf (depot kept, or the call's trace appended
   once, by YG00.v's depot_put); free_cf's is new here, through cgif's free-path functions (enqueue, the drain, the
   recycling loops), none of which touches st_depot. malloc_post_cf (YG07cf.v) and free_post_ycf (YG03cf.v) are not
   changed.
   Use (a Theorem Labs lane's driver, the loop entry of the wild count, a Theorem Labs lane's internal file WILD-COUNT.md 3.3 item 6): a driver whose
   allocator calls all carry FIXED traces keeps a depot of fixed traces, so the wild part stays empty up to its first
   entry call.
   Written in the driver lane on a Theorem Labs lane's request (00:5xZ), engine-shaped, for the engine owner to adopt.
   rule 24: no function proved. rule 24: proves no function (kind: allocator-model lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YGcfAmx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. A returning path satisfies every all-paths post (the same lemma as          *)
(*    YGcfRoomStep.v's ipost_apath, restated so this leaf needs no room layer).   *)
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
(* 2. The depot is kept by cgif's free-path functions (YG00.v) and grows by the   *)
(*    call's trace in free_cf (YG00cf.v). YGcfAmx.v's dep_* lemmas are global;     *)
(*    their hints are local there, so they are re-declared here.                  *)
Section DS.
Context {ci : CfImg} {cp : CfParams}.

Create HintDb dsdb.
#[local] Hint Resolve dep_ensure dep_mmu dep_populate dep_sec_alloc dep_depot_put : dsdb.

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

Lemma ds_drain_cf : forall s, ipost (maybe_drain_cf s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros s. unfold maybe_drain_cf. repeat ds_step. Qed.
#[local] Hint Resolve ds_drain_cf : dsdb.

(* free_cf: the depot is kept, or the call's trace is appended once (its depot_put). *)
Theorem ds_free_cf : forall p tr s, ipost (free_cf p tr s)
(fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr]).
Proof. intros p tr s. unfold free_cf. repeat ds_step. Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. THE DEPOT STEPS, on a returning model path.                                 *)
Theorem malloc_cf_depot_step : forall n tr s t p s',
  apath (malloc_cf n tr s) t (p, s') -> incl (st_depot s') (st_depot s ++ [tr]).
Proof.
intros n tr s t p s' Hp. pose proof (ds_ipost_apath _ _ _ _ (dep_malloc_cf n tr s) Hp) as D. cbn [snd] in D.
destruct D as [E|E]; rewrite E; [apply incl_appl, incl_refl | apply incl_refl].
Qed.

Theorem free_cf_depot_step : forall p tr s t u s',
  apath (free_cf p tr s) t (u, s') -> incl (st_depot s') (st_depot s ++ [tr]).
Proof.
intros p tr s t u s' Hp. pose proof (ds_ipost_apath _ _ _ _ (ds_free_cf p tr s) Hp) as D. cbn [snd] in D.
destruct D as [E|E]; rewrite E; [apply incl_appl, incl_refl | apply incl_refl].
Qed.

End DS.
