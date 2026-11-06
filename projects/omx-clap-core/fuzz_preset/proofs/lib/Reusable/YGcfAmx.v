(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the malloc / free laws in the
   form c-omx-alloc's generic kit consumes (alloc_model_laws_x_cf): a post with an UPPER bound on the event
   counter, which malloc_post_cf (YG07cf.v) and free_post_ycf (YG03cf.v) do not carry.
   The upper bounds, proved on every returning path of the model (ipost below, an all-paths property that
   needs no invariant):
   - malloc_cf: st_nev s' <= st_nev s + 3. malloc_cf ticks once (YG00cf.v:235). Its only other ticks are
     errb_map_cf's (YG00cf.v:123), reached through populate_cf -> map_more_user_cf's class-full arm ->
     errb_report_cf, at most once per malloc_cf. errb_report_cf makes two errb_append_cf calls, and each
     maps at most once: on a mapped buffer it remaps at most once; on an unmapped one it maps
     ERRB_INIT = 65,536 bytes, after which the capacity is 65,536 and the request (exh_len1 = 33 or
     exh_len2 c <= 70) fits, so the second map of that branch never runs. 3 is attained (a report on a
     mapped buffer whose two appends both overflow it).
   - free_cf: st_nev s' = st_nev s + 1 (free_post_ycf's equation): free_cf ticks once and its drain does
     not tick.
   No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfTok.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG06bcf YG07cf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG03cf YG03dcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. All-paths posts. ipost t P: every IRet of t satisfies P. It asks nothing of *)
(*    the requests, so it holds without any invariant; atok_cf_ipost adds it to an *)
(*    atok_cf post.                                                               *)
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

Create HintDb nevdb.

(* One step of an all-paths event bound: unfold the monad's primitives (by unfold: cbn refolds bind when
   its first component does not reduce), compute, split on a condition, or use a proved bound of a callee
   (hint database nevdb). *)
Ltac nev_unf :=
progress (unfold get_region, set_region, get_pc, set_pc, set_exh_cf, clear_exh_cf, init_cache_if_needed,
errb_set_size, errb_retire, tick, bind, get, put, modify, askz, ret, mcheck, fail, spin in *).

Ltac nev_cbn :=
cbn [ibind ipost fst snd st_nev set_regions set_cache set_chunks set_secs set_sec_arr set_sec_reserved set_depot
set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac nev_step :=
first
[ progress nev_cbn
| nev_unf
| progress intros
| match goal with |- ipost (ibind (ibind _ _) _) _ => apply ipost_ibind_assoc end
| match goal with |- ipost (ibind _ _) _ =>
apply ipost_ibind; eapply ipost_mono; [|solve [eauto with nevdb]];
let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hn" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- ipost _ _ =>
eapply ipost_mono; [|solve [eauto with nevdb]];
let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hn" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| lia ].

Lemma last_filter_app_cap : forall l x d, is_errb_cap x = true -> last (filter is_errb_cap (l ++ [x])) d = x.
Proof. intros l x d H. rewrite filter_app. cbn [filter]. rewrite H. cbv beta iota. apply last_last. Qed.

Section AMX.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma atok_cf_ipost {A} (t : itree astate A) : forall ns (Q : bool -> A -> Prop) (P : A -> Prop),
atok_cf ns t Q -> ipost t P -> atok_cf ns t (fun b a => Q b a /\ P a).
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [atok_cf ipost]; intros ns Q P H1 H2.
- split; assumption.
- destruct H1 as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH; [exact (Hk z Hz) | exact (H2 z)].
- exact H1.
- destruct H1.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The event bounds of malloc_cf's callees.                                     *)
Lemma nev_ensure : forall c need sof s,
ipost (ensure_free_array c need sof s) (fun r => st_nev (snd r) <= st_nev s + 0).
Proof. intros c need sof s. unfold ensure_free_array. repeat nev_step. Qed.
#[local] Hint Resolve nev_ensure : nevdb.

Lemma nev_mmu : forall c need s, ipost (map_more_user c need s) (fun r => st_nev (snd r) <= st_nev s + 0).
Proof. intros c need s. unfold map_more_user. repeat nev_step. Qed.
#[local] Hint Resolve nev_mmu : nevdb.

Lemma nev_populate : forall c need s, ipost (populate c need s) (fun r => st_nev (snd r) <= st_nev s + 0).
Proof. intros c need s. unfold populate. repeat nev_step. Qed.
#[local] Hint Resolve nev_populate : nevdb.

Lemma nev_sec_alloc : forall n s, ipost (sec_alloc n s) (fun r => st_nev (snd r) <= st_nev s + 0).
Proof. intros n s. unfold sec_alloc. repeat nev_step. Qed.
#[local] Hint Resolve nev_sec_alloc : nevdb.

Lemma nev_depot_put : forall tr s, ipost (depot_put tr s) (fun r => st_nev (snd r) <= st_nev s + 0).
Proof. intros tr s. unfold depot_put. repeat nev_step. Qed.
#[local] Hint Resolve nev_depot_put : nevdb.

(* errb_map_cf ticks once, and leaves the new capacity current. *)
Lemma nev_errb_map : forall w s, ipost (errb_map_cf w s)
(fun r => st_nev (snd r) <= st_nev s + 1 /\ errb_cap_cf (snd r) = Z.max 0 (round_up w kPage)).
Proof.
intros w s. unfold errb_map_cf. nev_unf. nev_cbn.
intros z. destruct (z =? 0); nev_cbn; [exact I|]. split; [lia|].
unfold errb_cap_cf, errb_e. cbn [st_secs set_secs set_nev].
rewrite last_filter_app_cap by reflexivity. reflexivity.
Qed.

(* One Printf: at most one map. On an unmapped buffer the first map gives 65,536 bytes, and a request of
   at most that size does not trigger the second. *)
Lemma nev_errb_append : forall len s, 0 <= len <= 65536 ->
ipost (errb_append_cf len s) (fun r => st_nev (snd r) <= st_nev s + 1).
Proof.
intros len s Hlen. unfold errb_append_cf. nev_unf. nev_cbn.
destruct (errb_mapped_cf s); cbn [negb] in *; nev_cbn.
- destruct (errb_cap_cf s <? errb_size_cf s + len); nev_cbn.
+ apply ipost_ibind. eapply ipost_mono; [|apply nev_errb_map]. intros [[] s1] [H1 _]. cbn [fst snd] in H1.
repeat nev_step.
+ repeat nev_step.
- apply ipost_ibind. eapply ipost_mono; [|apply nev_errb_map]. intros [[] s1] [H1 H2]. cbn [fst snd] in H1, H2.
nev_cbn. rewrite H2.
assert (E : Z.max 0 (round_up ERRB_INIT kPage) = 65536) by reflexivity. rewrite E.
destruct (Z.ltb_spec 65536 len) as [Hl|_]; [lia|].
repeat nev_step.
Qed.

(* The class-full report: two Printfs, so at most two maps. *)
Lemma nev_errb_report : forall c s, ipost (errb_report_cf c s) (fun r => st_nev (snd r) <= st_nev s + 2).
Proof.
intros c s. unfold errb_report_cf. nev_unf. nev_cbn.
destruct (exh_mem_cf s c); nev_cbn; [lia|].
apply ipost_ibind. eapply ipost_mono; [|apply nev_errb_append; unfold exh_len1; lia].
intros [[] s1] H1. cbn [fst snd] in H1. nev_cbn.
pose proof (ndigits_bounds c) as D1. pose proof (ndigits_bounds (class_size c)) as D2.
eapply ipost_mono; [|apply nev_errb_append; unfold exh_len2; lia].
intros [[] s2] H2. cbn [fst snd] in *. lia.
Qed.
#[local] Hint Resolve nev_errb_report : nevdb.

Lemma nev_mmu_cf : forall c need s, ipost (map_more_user_cf c need s) (fun r => st_nev (snd r) <= st_nev s + 2).
Proof. intros c need s. unfold map_more_user_cf. repeat nev_step. Qed.
#[local] Hint Resolve nev_mmu_cf : nevdb.

Lemma nev_populate_cf : forall c need s, ipost (populate_cf c need s) (fun r => st_nev (snd r) <= st_nev s + 2).
Proof. intros c need s. unfold populate_cf. repeat nev_step. Qed.
#[local] Hint Resolve nev_populate_cf : nevdb.

Lemma nev_gfa_cf : forall c n s, ipost (get_from_allocator_cf c n s) (fun r => st_nev (snd r) <= st_nev s + 2).
Proof. intros c n s. unfold get_from_allocator_cf. repeat nev_step. Qed.
#[local] Hint Resolve nev_gfa_cf : nevdb.

Lemma nev_refill_cf : forall c s, ipost (refill_if_empty_cf c s) (fun r => st_nev (snd r) <= st_nev s + 2).
Proof. intros c s. unfold refill_if_empty_cf. repeat nev_step. Qed.
#[local] Hint Resolve nev_refill_cf : nevdb.

Lemma nev_cache_alloc_cf : forall c s, ipost (cache_alloc_cf c s) (fun r => st_nev (snd r) <= st_nev s + 2).
Proof. intros c s. unfold cache_alloc_cf. repeat nev_step. Qed.
#[local] Hint Resolve nev_cache_alloc_cf : nevdb.

(* malloc_cf: its own tick plus at most two errbuf maps. *)
Theorem nev_malloc_cf : forall n tr s, ipost (malloc_cf n tr s) (fun r => st_nev (snd r) <= st_nev s + 3).
Proof. intros n tr s. unfold malloc_cf. repeat nev_step. Qed.

(* ---------------------------------------------------------------------------- *)
(* 2b. The depot growth of malloc_cf, on every returning path: the depot is kept,  *)
(*    or the call's own trace is appended once (depot_put). Its callees keep the  *)
(*    depot. realloc_tree_with needs it: its free runs on malloc_cf's result, and *)
(*    admits_keep (YG01.v) carries the call's trace premise across exactly this.  *)
Create HintDb depdb.

Ltac dep_cbn :=
cbn [ibind ipost fst snd st_depot set_regions set_cache set_chunks set_secs set_sec_arr set_sec_reserved set_depot
set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac dep_step :=
first
[ progress dep_cbn
| nev_unf
| progress intros
| match goal with |- ipost (ibind (ibind _ _) _) _ => apply ipost_ibind_assoc end
| match goal with |- ipost (ibind _ _) _ =>
apply ipost_ibind; eapply ipost_mono; [|solve [eauto with depdb]];
let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hd" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- ipost _ _ =>
eapply ipost_mono; [|solve [eauto with depdb]];
let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hd" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| match goal with H : _ \/ _ |- _ => destruct H end
| solve [reflexivity | congruence | left; congruence | right; congruence] ].

Lemma dep_ensure : forall c need sof s, ipost (ensure_free_array c need sof s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need sof s. unfold ensure_free_array. repeat dep_step. Qed.
#[local] Hint Resolve dep_ensure : depdb.

Lemma dep_mmu : forall c need s, ipost (map_more_user c need s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need s. unfold map_more_user. repeat dep_step. Qed.
#[local] Hint Resolve dep_mmu : depdb.

Lemma dep_populate : forall c need s, ipost (populate c need s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need s. unfold populate. repeat dep_step. Qed.
#[local] Hint Resolve dep_populate : depdb.

Lemma dep_sec_alloc : forall n s, ipost (sec_alloc n s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros n s. unfold sec_alloc. repeat dep_step. Qed.
#[local] Hint Resolve dep_sec_alloc : depdb.

Lemma dep_depot_put : forall tr s, ipost (depot_put tr s)
(fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr]).
Proof. intros tr s. unfold depot_put. repeat dep_step. Qed.
#[local] Hint Resolve dep_depot_put : depdb.

Lemma dep_errb_map : forall w s, ipost (errb_map_cf w s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros w s. unfold errb_map_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_errb_map : depdb.

Lemma dep_errb_append : forall len s, ipost (errb_append_cf len s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros len s. unfold errb_append_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_errb_append : depdb.

Lemma dep_errb_report : forall c s, ipost (errb_report_cf c s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c s. unfold errb_report_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_errb_report : depdb.

Lemma dep_mmu_cf : forall c need s, ipost (map_more_user_cf c need s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need s. unfold map_more_user_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_mmu_cf : depdb.

Lemma dep_populate_cf : forall c need s, ipost (populate_cf c need s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c need s. unfold populate_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_populate_cf : depdb.

Lemma dep_gfa_cf : forall c n s, ipost (get_from_allocator_cf c n s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c n s. unfold get_from_allocator_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_gfa_cf : depdb.

Lemma dep_refill_cf : forall c s, ipost (refill_if_empty_cf c s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c s. unfold refill_if_empty_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_refill_cf : depdb.

Lemma dep_cache_alloc_cf : forall c s, ipost (cache_alloc_cf c s) (fun r => st_depot (snd r) = st_depot s).
Proof. intros c s. unfold cache_alloc_cf. repeat dep_step. Qed.
#[local] Hint Resolve dep_cache_alloc_cf : depdb.

Theorem dep_malloc_cf : forall n tr s, ipost (malloc_cf n tr s)
(fun r => st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr]).
Proof. intros n tr s. unfold malloc_cf. repeat dep_step. Qed.

(* The same on a returning path: what an apath of malloc_cf ends in (the instance's realloc U at the post-malloc
   state, YGcfRmodel.v). *)
Lemma ipost_apath_amx : forall {A} (t : itree astate A) (P : A -> Prop) tr a, ipost t P -> apath t tr a -> P a.
Proof.
intros A t P. induction t as [a' | q sn k IH | pc | f]; intros tr a H Hp.
- destruct tr; cbn [apath] in Hp; [subst a'; exact H | destruct Hp].
- destruct tr as [|[q' z] tr']; cbn [apath] in Hp; [destruct Hp|]. destruct Hp as (_ & _ & Hp).
  exact (IH z tr' a (H z) Hp).
- destruct tr; cbn [apath] in Hp; destruct Hp.
- destruct tr; cbn [apath] in Hp; destruct Hp.
Qed.

Theorem dep_malloc_cf_apath : forall n tr s trc r, apath (malloc_cf n tr s) trc r ->
st_depot (snd r) = st_depot s \/ st_depot (snd r) = st_depot s ++ [tr].
Proof. intros n tr s trc r H. exact (ipost_apath_amx _ _ _ _ (dep_malloc_cf n tr s) H). Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The kit's malloc / free laws.                                               *)
Definition malloc_post_amx (s : astate) (n : Z) (r : sptr * astate) : Prop :=
let (p, s') := r in
st_nev s <= st_nev s' <= st_nev s + 3 /\ (length (st_secs s) <= length (st_secs s'))%nat /\ frames s' = frames s /\
match p with PNull => blocks s' = blocks s | _ => blocks s' = blocks s ++ [(p, n)] end.

Theorem amx_malloc_cf : forall U s n tr,
universe_ok U -> Wf_cf U s -> qtight s -> ROOM_cf s -> 0 <= n < cf_malloc_max -> blocks_bytes s + n <= LIVE_MAX -> admits U tr s ->
atok_cf true (malloc_cf n tr s) (fun _ r => malloc_post_amx s n r).
Proof.
intros U s n tr HU W HQ HR Hn Hlive Htr. unfold ROOM_cf in HR. destruct HR as [R1 [R2 R3]].
pose proof (malloc_ok_cf U s n tr HU W Hn Hlive Htr R1 R2 R3) as A.
pose proof (atok_cf_ipost _ true _ _ A (nev_malloc_cf n tr s)) as B.
eapply atok_cf_mono; [|exact B]. intros b [p s'] [Hp Hnev]. cbn [snd] in Hnev.
unfold malloc_post_cf in Hp. cbv beta iota in Hp. destruct Hp as (_ & Nlo & [Hlen _] & Hfr & Hbl & _).
unfold malloc_post_amx. cbv beta iota.
split; [lia|]. split; [exact Hlen|]. split; [exact Hfr|].
destruct p; cbv beta iota in Hbl |- *; first [exact Hbl | exact (proj1 Hbl)].
Qed.

Definition free_post_amx (s : astate) (p : sptr) (n : Z) (r : unit * astate) : Prop :=
let s' := snd r in
st_nev s <= st_nev s' <= st_nev s + 1 /\ (length (st_secs s) <= length (st_secs s'))%nat /\ frames s' = frames s /\
(exists l1 l2, ((p = PNull /\ l1 ++ l2 = blocks s) \/ blocks s = l1 ++ (p, n) :: l2) /\ blocks s' = l1 ++ l2).

Theorem amx_free_cf : forall U s p n tr,
universe_ok U -> Wf_cf U s -> qtight s -> ROOM_cf s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok_cf true (free_cf p tr s) (fun _ r => free_post_amx s p n r).
Proof.
intros U s p n tr HU W HQ HR Hp Htr. unfold ROOM_cf in HR. destruct HR as [R1 [R2 R3]].
eapply atok_cf_mono; [|eapply ml_free_cf; eauto].
intros b [[] s'] H. unfold free_post_ycf in H. unfold free_post_amx. cbn [snd] in H |- *.
destruct H as (_ & Hnev & Hx & Hfr & Hbl & _).
split; [lia|]. split; [exact (proj1 (secs_ext_cf_of_secs_ext _ _ Hx))|]. split; [exact Hfr | exact Hbl].
Qed.
End AMX.
