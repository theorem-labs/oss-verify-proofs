(* CARRIED from commit ae2fa80b0325f09472155bcfce1c36e649d6ff60,
   proofs/cgif/cgif_file_fuzzer/lib/YG01cf.v, sha256 2095ee6b5c9f86335bc49d7af33622d40ebff459946c0d4968ffaded631867dc (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
(* prefix-only copy of proofs/omx-clap-core/fuzz_preset/lib/Reusable/YG01cf.v@6e9ff2e6573c487199f2990b43c5e19cce86e581, do not edit (single writer: a Theorem Labs lane; send change requests to a Theorem Labs lane as diffs). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: WfP_cf gains wfc_qsize, every quarantined item is at most kQuarantineMax
   (free_cf's enqueue arm, YG00cf.free_cf's size test); WfP_cf_of_WfP derives it from cgif's MALLOC_MAX. *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the STATE INVARIANT.
   Wf_cf is cgif's Wf (YG01.v:431-454) re-keyed on LIVE state, so that it holds at preset's event counts
   (about 3.0e7 allocator events per harness call, where cgif's regime admits at most 8,192).
   cgif's YG01.v is NOT edited and NOT weakened: Wf_cf_of_Wf below shows cgif's invariant implies this one.
   No address: every numeral here is a cgif content constant (YG00.v:10-43) or a cf constant of YGcfNames.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames YG00cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section WFCF.
Context {cp : CfParams}.
Variable U : Univ.

(* cgif's cls_ok (YG01.v:367-381), one field re-based.
   wr_mapped_bound (:273) is `rg_mapped_user r <= kUserMapSize * EV_MAX` = 2 GiB per class.
   Preset's class 17 maps 3,584 MiB (measured, an internal record, omx-clap-core-2.md:27-47), so that field is
   FALSE before the class even fills. wrc_mapped_bound is the bound the real class-full arm maintains:
   the arm tests `rg_mapped_user r + map_size <=? kFreeArrayOffset` BEFORE mapping (YG00.v:285), so what
   holds of every reachable state is `rg_mapped_user r <= kFreeArrayOffset`. The map_size term belongs to
   the arm's own test, not to the invariant: at class 17 the two differ, since 3,584 MiB IS kFreeArrayOffset
   and `+ kUserMapSize <= kFreeArrayOffset` would be false there. *)
Record cls_ok_cf (c : Z) (r : region) (p : pclass) (inited : bool) (ko bo : list Z) : Prop := {
wrc_alloc : 0 <= rg_alloc_user r <= rg_mapped_user r;
wrc_carved : rg_mapped_user r - rg_alloc_user r < kUserMapSize + kMaxSize;
wrc_mapped_al : rg_mapped_user r mod kUserMapSize = 0;
wrc_alloc_al : rg_alloc_user r mod class_size c = 0;
wrc_fa : 0 <= rg_mapped_fa r /\ rg_mapped_fa r mod kFreeArrayMapSize = 0;
wrc_fa_bound : rg_mapped_fa r <= kFreeArrayMax;
wrc_fa_len : 4 * fa_len (rg_free r) <= rg_mapped_fa r;
wrc_runs : Forall (fun f => match f with FRun lo k => 1 <= k | FOne _ => True end) (rg_free r);
wrc_nodup : NoDup (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo);
wrc_elems : Forall (fun o => 0 <= o < rg_alloc_user r /\ o mod class_size c = 0)
(fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo);
(* cgif's wr_holes (YG01.v:378) has hole_ok = False. A cf class may carry ONE hole: the sentinel
   (EXH_HOLE, 0) of YG00cf.v, which encodes the class's exhausted byte. *)
wrc_holes : Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes r) /\ NoDup (rg_holes r);
wrc_cache : if inited then pc_max p = max_cached c /\ Z.of_nat (length (pc_chunks p)) <= max_cached c else p = pclass0;
wrc_mapped_bound : rg_mapped_user r <= kFreeArrayOffset
}.

Definition wf_class_cf (s : astate) (c : Z) : Prop :=
cls_ok_cf c (reg s c) (cache s c) (st_cache_inited s) (chunk_offs s c) (batch_offs s c).

(* NO free-array room field. cgif's wf_fa_room (YG01.v:449-450) asserts the free array is mapped for
   EVERY record of a class plus 2 * (EV_MAX - st_nev) spare slots. That is kept only by the event term or
   by regime_big's record cap, both gone here, and it is FALSE on reachable states: populate's
   ensure_free_array maps only 4 * (fa_len + new_cnt), the FREE entries (YG00.v:263-266), as the real
   EnsureFreeArraySpace sizes on num_freed_chunks. (Class 32 B, malloc with nothing free: each populate
   carves 8,192 with fa_len <= 8, rg_mapped_fa stays 262,144 = 65,536 entries, and after the 8th
   populate the class holds 65,536 records.) What ensure_free_array DOES keep is cls_ok_cf's own
   wrc_fa_len (4 * fa_len <= rg_mapped_fa, cgif's wr_fa_len YG01.v:374), and the growth's capacity check
   (new_mapped <= kFreeArrayMax, YG00.v:267) follows from nrec_bound_cf below, since kFreeArrayMax = 2 ^ 29
   is a multiple of kFreeArrayMapSize = 2 ^ 18. The free path may therefore GROW the free array
   (return_to_allocator, YG00.v:461-466, spin_on_fail = true): a real KMapFreeArray, granted or refused
   (a spin, which atok permits). cgif's regime_big lemmas (ml_malloc_big / ml_free_big, YG0d.v:523-526)
   carry the caps this instance drops and must NEVER be cited. *)

(* cgif's wf_sec (YG01.v:408-416) with ONE clause re-based: ws_lens caps every secondary
   at SEC_LEN_MAX = 2 ^ 28 + 2 ^ 14, which fuzz_reply's 2 ^ 29 request exceeds. The cf cap
   is cf_nob, the placement lemma's own bound, so a new secondary closes straight from
   CfParams' cf_sizes_ok (sec_map_size n <= cf_nob) with no monotonicity lemma.
   wsc_arr_live is cgif's ws_arr_live UNCHANGED: the errbuf control entries of YG00cf.v
   carry sm_live = false, so they fall outside the equivalence and need no exemption. *)
Record wf_sec_cf (s : astate) : Prop := {
wsc_nodup : NoDup (st_sec_arr s);
wsc_arr_chunks : forall r, In r (st_sec_arr s) <-> exists k, In k (st_chunks s) /\ ck_beg k = PSec r kPage;
wsc_arr_live : forall r, In r (st_sec_arr s) <->
exists sm, nth_error (st_secs s) r = Some sm /\ sm_live sm = true;
wsc_reserved : Z.of_nat (length (st_sec_arr s)) <= st_sec_reserved s <= kPtrArrayEntriesPerCommit;
wsc_reserved_al : 0 <= st_sec_reserved s /\ st_sec_reserved s mod kPtrArrayEntriesPerCommit = 0;
wsc_lens : Forall (fun sm => 0 <= sm_len sm <= cf_nob) (st_secs s)
}.

Lemma wf_sec_cf_ext : forall s s', st_sec_arr s' = st_sec_arr s -> st_secs s' = st_secs s ->
st_chunks s' = st_chunks s -> st_sec_reserved s' = st_sec_reserved s -> wf_sec_cf s -> wf_sec_cf s'.
Proof.
intros s s' E1 E2 E3 E4 H. constructor; rewrite ?E1, ?E2, ?E3, ?E4.
- exact (wsc_nodup _ H).
- exact (wsc_arr_chunks _ H).
- exact (wsc_arr_live _ H).
- exact (wsc_reserved _ H).
- exact (wsc_reserved_al _ H).
- exact (wsc_lens _ H).
Qed.

Lemma wf_sec_cf_of_wf_sec : forall s, wf_sec s -> wf_sec_cf s.
Proof.
intros s H. constructor.
- exact (ws_nodup _ H).
- exact (ws_arr_chunks _ H).
- exact (ws_arr_live _ H).
- exact (ws_reserved _ H).
- exact (ws_reserved_al _ H).
- eapply Forall_impl; [|exact (ws_lens _ H)]. cbv beta. intros sm Hsm.
pose proof cf_nob_sec_len. unfold SEC_LEN_MAX in *. lia.
Qed.

(* cgif's chunk_ok (YG01.v:387-396) opens with `0 <= ck_req k < MALLOC_MAX`, so a chunk
   of a request at or above 2 ^ 28 would break Wf_cf. The cf form replaces that one
   conjunct by cf_malloc_max and keeps the rest verbatim. *)
Definition chunk_ok_cf (s : astate) (k : chunk) : Prop :=
0 <= ck_req k < cf_malloc_max /\
match ck_beg k with
| PPrim off => from_primary (ck_req k) = true /\ prim_class off = chunk_class (ck_req k) /\
0 <= off - region_off (prim_class off) < 2 ^ 32
| PSec r off => from_primary (ck_req k) = false /\ off = kPage /\
exists sm, nth_error (st_secs s) r = Some sm /\ sm_live sm = true /\
sm_size sm = needed_size (ck_req k) /\ sm_len sm = sec_map_size (ck_req k)
| _ => False
end.

Lemma chunk_ok_cf_ext : forall s s' k, st_secs s' = st_secs s -> chunk_ok_cf s k -> chunk_ok_cf s' k.
Proof. intros s s' k E H. unfold chunk_ok_cf in *. rewrite E. exact H. Qed.

Lemma chunk_ok_cf_of_chunk_ok : forall s k, chunk_ok s k -> chunk_ok_cf s k.
Proof.
intros s k H. unfold chunk_ok, chunk_ok_cf in *. destruct H as [H1 H2].
split; [pose proof cf_malloc_max_ge; unfold MALLOC_MAX in *; lia | exact H2].
Qed.

(* cgif's WfP (YG01.v:431-453). KEPT VERBATIM: the four event fields, which are LOWER bounds on st_nev
   (wf_chunks_ev :331, wf_prim_ev :332, wf_batches_ev :335, wf_secs_ev :344) and so stay true as events grow.
   DROPPED: wf_regime (:345), an UPPER bound on st_nev, and wf_fa_room (:342), which is false on live state
   (see above). CHANGED: wf_classes (:328) to wf_class_cf, wf_chunks to chunk_ok_cf, wf_secondary to
   wf_sec_cf. ADDED: wfc_compl0, and wfc_sec_live, which replaces sec_arr_small (YG07.v:252-256, derived
   there from st_nev <= EV_MAX). *)
Record WfP_cf (pp cc bb : Z) (s : astate) : Prop := {
wfc_len_regions : length (st_regions s) = 32%nat;
wfc_len_cache : length (st_cache s) = 32%nat;
wfc_reg0 : reg s 0 = region0;
wfc_classes : forall c, 1 <= c <= 31 -> wf_class_cf s c;
wfc_chunks : Forall (chunk_ok_cf s) (st_chunks s);
wfc_chunks_nodup : NoDup (map ck_beg (st_chunks s));
wfc_chunks_ev : Z.of_nat (length (st_chunks s)) + cc <= st_nev s;
wfc_prim_ev : prim_user_mapped s + kUserMapSize * pp <= kUserMapSize * st_nev s;
wfc_live : blocks_bytes s <= LIVE_MAX;
wfc_quarantine : wf_quar s;
wfc_batches_ev : Z.of_nat (length (all_batches s)) + bb <= st_nev s;
wfc_secondary : wf_sec_cf s;
wfc_fakestack : wf_fs s;
wfc_depot : depot_fits U (st_depot s);
wfc_nev : 0 <= st_nev s;
wfc_slack : 0 <= pp /\ 0 <= cc /\ 0 <= bb;
wfc_qinited : all_batches s <> [] -> st_cache_inited s = true;
wfc_secs_ev : Z.of_nat (length (st_secs s)) + cc <= st_nev s;
wfc_compl0 : Compl0 s;
(* The count INCLUDES secondaries that are freed but still quarantined, hence still
   mapped: an entry leaves st_sec_arr only at the quarantine recycle (sec_dealloc,
   YG00.v:481-494, reached from recycle_chunk YG00.v:510 through maybe_drain), never at
   free (YG00.v:548-566, which only marks the chunk CQuarantined and enqueues it).
   For preset (PresetOomRoom, a Theorem Labs lane's oomroom SEC-PROOF record): the
   walk-dischargeable bound is live_sec(x) <= 3 * floor(N / 1026) + 9 + floor(Q / 64513), 13,367
   at N = 3 MiB and Q = 256 MiB (realizable worst case 8,771 with quarantine), so preset's
   instance takes cf_sec_live_max = 16,000: above 13,367 + 1 for the strict call premise, below
   kPtrArrayEntriesPerCommit = 16,384 (cf_sec_live_commit), and below c-asan's placement limit
   80,953 at NOB = 2 ^ 29. Each other unit's instance records its own value against its own walk-provable
   count (an earlier note here quoted a figure for reply that was never an instance derivation).
   NOT maintained by the allocator alone: a secondary malloc appends an entry, so the
   call forms carry the premise (see acall_pre_cf). *)
wfc_sec_live : Z.of_nat (length (st_sec_arr s)) <= cf_sec_live_max;
(* every quarantined item is at most the quarantine's max_size: free_cf enqueues only on its size test's enqueue
   arm (YG00cf.free_cf, `ck_n k' <=? kQuarantineMax`; compiler-rt sanitizer_quarantine.h:98); the drain's merge,
   transfer and pop only move or drop items *)
wfc_qsize : Forall (fun k => ck_n k <= kQuarantineMax) (q_items s)
}.

Definition Wf_cf : astate -> Prop := WfP_cf 0 0 0.
End WFCF.

(* wfc_qsize reads only the two queues *)
Lemma qsize_ext : forall s s', st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s ->
Forall (fun k => ck_n k <= kQuarantineMax) (q_items s) -> Forall (fun k => ck_n k <= kQuarantineMax) (q_items s').
Proof. intros s s' E1 E2 H. unfold q_items, all_batches in *. rewrite E1, E2. exact H. Qed.

(* ---------------------------------------------------------------------------- *)
(* cgif's invariant IMPLIES this one, so no state cgif admits is lost.            *)
(* kUserMapSize * EV_MAX = 2^18 * 2^13 = 2^31 = 2,147,483,648 <= kFreeArrayOffset *)
(* = 3,758,096,384, so the re-based field is strictly weaker; the two added       *)
(* fields are the extra hypotheses.                                              *)
Lemma cls_ok_cf_of_cls_ok : forall c r p inited ko bo,
cls_ok c r p inited ko bo -> cls_ok_cf c r p inited ko bo.
Proof.
intros c r p inited ko bo C. constructor; try (exact (wr_alloc _ _ _ _ _ _ C));
try (exact (wr_carved _ _ _ _ _ _ C)); try (exact (wr_mapped_al _ _ _ _ _ _ C));
try (exact (wr_alloc_al _ _ _ _ _ _ C)); try (exact (wr_fa _ _ _ _ _ _ C));
try (exact (wr_fa_bound _ _ _ _ _ _ C)); try (exact (wr_fa_len _ _ _ _ _ _ C));
try (exact (wr_runs _ _ _ _ _ _ C)); try (exact (wr_nodup _ _ _ _ _ _ C));
try (exact (wr_elems _ _ _ _ _ _ C)); try (exact (wr_cache _ _ _ _ _ _ C)).
- pose proof (wr_holes _ _ _ _ _ _ C) as [Hh Hnd]. split; [|exact Hnd].
eapply Forall_impl; [|exact Hh]. intros h Hho. destruct Hho.
- pose proof (wr_mapped_bound _ _ _ _ _ _ C) as M. unfold kUserMapSize, EV_MAX, kFreeArrayOffset in *. lia.
Qed.

Lemma wf_class_cf_of_wf_class : forall s c, wf_class s c -> wf_class_cf s c.
Proof. intros s c H. apply cls_ok_cf_of_cls_ok, H. Qed.

Section WFCF2.
Context {cp : CfParams}.

Lemma WfP_cf_of_WfP : forall U pp cc bb s,
WfP U pp cc bb s -> Compl0 s -> Z.of_nat (length (st_sec_arr s)) <= cf_sec_live_max ->
WfP_cf U pp cc bb s.
Proof.
intros U pp cc bb s W HC HS. constructor;
try (exact (wf_len_regions _ _ _ _ _ W)); try (exact (wf_len_cache _ _ _ _ _ W));
try (exact (wf_reg0 _ _ _ _ _ W)); try (exact (wf_chunks _ _ _ _ _ W));
try (exact (wf_chunks_nodup _ _ _ _ _ W)); try (exact (wf_chunks_ev _ _ _ _ _ W));
try (exact (wf_prim_ev _ _ _ _ _ W)); try (exact (wf_live _ _ _ _ _ W));
try (exact (wf_quarantine _ _ _ _ _ W)); try (exact (wf_batches_ev _ _ _ _ _ W));
try (exact (wf_secondary _ _ _ _ _ W)); try (exact (wf_fakestack _ _ _ _ _ W));
try (exact (wf_depot _ _ _ _ _ W)); try (exact (wf_nev _ _ _ _ _ W));
try (exact (wf_slack _ _ _ _ _ W)); try (exact (wf_qinited _ _ _ _ _ W));
try (exact (wf_secs_ev _ _ _ _ _ W)); try exact HC; try exact HS;
try (exact (wf_sec_cf_of_wf_sec _ (wf_secondary _ _ _ _ _ W)));
try (eapply Forall_impl; [|exact (wf_chunks _ _ _ _ _ W)]; cbv beta;
intros k Hk; exact (chunk_ok_cf_of_chunk_ok _ _ Hk)).
- intros c Hc. apply wf_class_cf_of_wf_class. exact (wf_classes _ _ _ _ _ W c Hc).
- (* cgif's chunks are below MALLOC_MAX = kQuarantineMax, and every quarantined item is a chunk *)
  apply Forall_forall. intros k Hk.
  destruct (proj1 (Forall_forall _ _) (wq_items _ (wf_quarantine _ _ _ _ _ W)) k Hk) as [Hin _].
  destruct (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k Hin) as [Hr _].
  unfold ck_n, req_size, MALLOC_MAX, kQuarantineMax in *. destruct (ck_req k =? 0); lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* The initial state.                                                            *)
(* the init witness of wfc_qsize: the initial quarantine holds no item *)
Lemma qsize_init_cf : Forall (fun k => ck_n k <= kQuarantineMax) (q_items init_state).
Proof. unfold q_items, all_batches. cbn. constructor. Qed.

Lemma wf_init_cf : forall U, Wf_cf U init_state.
Proof.
intros U. unfold Wf_cf. apply WfP_cf_of_WfP.
- exact (wf_init U).
- exact (proj1 BigInv_init).
- cbn. pose proof cf_sec_live_nonneg. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* The NAMED bounds. A walk discharges these by name; none is hidden inside the   *)
(* record, which is what c-asan's placement lemma asked for.                      *)
Lemma mapped_bound_cf : forall U pp cc bb s c,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> rg_mapped_user (reg s c) <= kFreeArrayOffset.
Proof.
intros U pp cc bb s c W Hc. exact (wrc_mapped_bound _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c Hc)).
Qed.

Lemma sec_live_bound_cf : forall U pp cc bb s,
WfP_cf U pp cc bb s -> Z.of_nat (length (st_sec_arr s)) <= cf_sec_live_max.
Proof. intros U pp cc bb s W. exact (wfc_sec_live _ _ _ _ _ W). Qed.

Lemma live_bound_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> blocks_bytes s <= LIVE_MAX.
Proof. intros U pp cc bb s W. exact (wfc_live _ _ _ _ _ W). Qed.

Lemma class_size_32 : forall c, 1 <= c <= 31 -> 32 <= class_size c.
Proof.
intros c Hc. pose proof (class_ok c Hc) as (K1 & K2 & _).
pose proof (Z.div_mod (class_size c) 32 ltac:(lia)) as D. rewrite K2 in D. lia.
Qed.

(* cgif bounds the records of a class through the event counter (nrecZ_small,
   YG07.v:246: nrecZ s c + 10248 <= 65536). That is FALSE for preset: class 17 at
   3,584 MiB mapped, class_size 768, carries up to 4.89e6 records, 88 times that cap.
   The instance does not need it. The free array holds every record of every class
   from the re-based bound alone: class_size c >= 32, so
   4 * records <= 4 * kFreeArrayOffset / 32 = 469,762,048 <= kFreeArrayMax = 536,870,912. *)
Lemma nrec_bound_cf : forall U pp cc bb s c,
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
class_size c * Z.of_nat (length (class_elems s c)) <= kFreeArrayOffset /\
4 * Z.of_nat (length (class_elems s c)) <= kFreeArrayMax.
Proof.
intros U pp cc bb s c W Hc.
pose proof (wfc_compl0 _ _ _ _ _ W c Hc) as HC. unfold cdef in HC.
pose proof (wrc_alloc _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c Hc)) as [A1 A2].
pose proof (mapped_bound_cf U pp cc bb s c W Hc) as M.
pose proof (class_size_32 c Hc) as CS.
pose proof (Nat2Z.is_nonneg (length (class_elems s c))) as LN.
set (L := Z.of_nat (length (class_elems s c))) in *.
assert (E : class_size c * L = rg_alloc_user (reg s c)) by lia.
assert (H32 : 32 * L <= class_size c * L) by nia.
split; [lia|]. unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* Slack weakening, the cf form of YG06.v:197-201 / AFf2.v:131-136.               *)
Lemma WfP_cf_weaken : forall U pp cc bb pp' cc' bb' s,
WfP_cf U pp cc bb s -> 0 <= pp' <= pp -> 0 <= cc' <= cc -> 0 <= bb' <= bb -> WfP_cf U pp' cc' bb' s.
Proof.
intros U pp cc bb pp' cc' bb' s W H1 H2 H3. constructor;
try (exact (wfc_len_regions _ _ _ _ _ W)); try (exact (wfc_len_cache _ _ _ _ _ W));
try (exact (wfc_reg0 _ _ _ _ _ W)); try (exact (wfc_classes _ _ _ _ _ W));
try (exact (wfc_chunks _ _ _ _ _ W)); try (exact (wfc_chunks_nodup _ _ _ _ _ W));
try (exact (wfc_live _ _ _ _ _ W)); try (exact (wfc_quarantine _ _ _ _ _ W));
try (exact (wfc_secondary _ _ _ _ _ W)); try (exact (wfc_fakestack _ _ _ _ _ W));
try (exact (wfc_depot _ _ _ _ _ W)); try (exact (wfc_nev _ _ _ _ _ W));
try (exact (wfc_qinited _ _ _ _ _ W)); try (exact (wfc_compl0 _ _ _ _ _ W));
try (exact (wfc_sec_live _ _ _ _ _ W)); try (exact (wfc_qsize _ _ _ _ _ W)).
- pose proof (wfc_chunks_ev _ _ _ _ _ W). lia.
- pose proof (wfc_prim_ev _ _ _ _ _ W). unfold kUserMapSize in *. nia.
- pose proof (wfc_batches_ev _ _ _ _ _ W). lia.
- lia.
- pose proof (wfc_secs_ev _ _ _ _ _ W). lia.
Qed.
End WFCF2.
