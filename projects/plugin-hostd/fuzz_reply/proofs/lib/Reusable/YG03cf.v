(* CARRIED from commit 67b1573c554b41c3694e495821c6dc8e452f7d63,
   proofs/cgif/cgif_file_fuzzer/lib/YG03cf.v, sha256 a24dfc0f418c8243c3f8b4245751d728c4cd7a434c2779714c950bc836752578 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change made here is the module
   prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: cache_dealloc_post_cf gains `st_cache_inited s' = true` (cache_dealloc
   starts with init_cache_if_needed, as cache_alloc_post_y3 already states); cache_dealloc_ok_cf proves it. recycle_post_cf
   gains `st_cache_inited s = true -> st_cache_inited s' = true` (recycle_chunk's primary arm is that cache_dealloc; its
   secondary arm, sec_dealloc, leaves the flag); recycle_chunk_okx_cf proves it. *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: WfR_cf gains wfr_qsize (WfP_cf's wfc_qsize); WfR_qpush_cf, enqueue_okx_cf and
   enqueue_ok_cf take `ck_n kq <= kQuarantineMax` (free_cf's enqueue arm supplies it). *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: free_with_cf takes Quarantine::Put's size test (as YG00cf.free_cf), and
   free_gen_cf proves its recycle side from recycle_chunk_okx_cf; statements unchanged. A change request to a Theorem Labs lane. *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG03.v, with its module paths changed; its addresses are still cgif_file_fuzzer.asan's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG03.v, re-keyed from cgif's Wf to fuzz_preset's
   event-free invariant Wf_cf (YG01cf.v), with no bound on st_nev. Names carry the suffix _cf (_y3 for the local copies of the
   upcoming YG02cf / YG07cf lemmas). Changed: every wf_fa_room / 2 * (EV_MAX - st_nev s) room thread is deleted (the free-array
   push maps more through ensure_free_array, whose grant keeps wrc_fa_len and whose refusal spins); every wf_regime / BigP /
   regime conjunct is deleted; the cache_alloc premise preg is replaced by the class's user-map room; the intermediate states use
   WfR_cf (WfP_cf without wfc_compl0) and cdef is tracked as in cgif's x-posts; the drain step is an interface
   (drain_spec_cf below, met by maybe_drain_cf in YG03dcf.v) and the free theorem is stated for any drain that meets it; a
   recycled batch may be empty (MergeBatches' extracted ones), so RI_cf / RIx_cf keep only the upper bound on its items.
   The YG02 / YG06 / YG07 lemmas that free needs are re-proved here over WfR_cf. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfTok.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Ltac cbnr := cbn [rg_mapped_user rg_alloc_user rg_mapped_fa rg_free rg_holes fst snd].
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.

Section YG03CF.
Context {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* THE DRAIN STEP, as an interface. cgif's maybe_drain IFails (its mcheck,       *)
(* YG00.v:544) exactly where the runtime's Quarantine::Recycle runs              *)
(* MergeBatches; the cf model's maybe_drain_cf (YG00cf.v) runs the merge. free   *)
(* is proved here for every drain md that meets drain_spec_cf (free_with_cf /    *)
(* ml_free_with_cf); YG03dcf.v proves drain_spec_cf U maybe_drain_cf.           *)
Definition fframe_cf (s s' : astate) : Prop :=
st_nev s' = st_nev s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\ blocks s' = blocks s /\ secs_ext s s'.
Definition unq_cf (s : astate) : Z := quar_n s - queued_n s.
Definition drain_spec_cf (U : Univ) (md : M unit) : Prop :=
forall pp cc bb s ns, WfP_cf U pp cc bb s ->
atok ns (md s) (fun ns' res => WfP_cf U pp cc bb (snd res) /\ fframe_cf s (snd res) /\
qc_bytes (st_qthread (snd res)) <= kQuarantineCacheMax /\
qc_bytes (st_qglobal (snd res)) <= Z.max (qc_bytes (st_qglobal s)) kQuarantineMax /\ unq_cf (snd res) = unq_cf s).

(* cgif's free_post (YG01.v:457-461) with Wf -> Wf_cf. *)
Definition free_post_ycf (U : Univ) (s : astate) (p : sptr) (n : Z) (ns : bool) (r : unit * astate) : Prop :=
let s' := snd r in
Wf_cf U s' /\ st_nev s' = st_nev s + 1 /\ secs_ext s s' /\ frames s' = frames s /\
(exists l1 l2, ((p = PNull /\ l1 ++ l2 = blocks s) \/ blocks s = l1 ++ (p, n) :: l2) /\ blocks s' = l1 ++ l2) /\
(qtight s -> qtight s').

(* free_cf (YG00cf.v) with its drain as a parameter: free_cf is free_with_cf maybe_drain_cf (YG03dcf.v). It is
   cgif's free (YG00.v:548-566) with the two not-live checks tagged FModel, and with Quarantine::Put's size test:
   a chunk above kQuarantineMax (the max_size cell) is recycled at once (YG00cf.v's free_cf comment). *)
Definition free_with_cf (md : M unit) (p : sptr) (trace : list Z) : M unit :=
tick ;;
s <- get ;;
(if st_internal_inited s then ret tt else modify (set_internal_inited true)) ;;
match p with
| PNull => ret tt
| _ =>
s <- get ;;
match find_user (st_chunks s) p with
| None => fail (FModel 11)
| Some k =>
(if match ck_state k with CAllocated => true | _ => false end then ret tt else fail (FModel 12)) ;;
depot_put trace ;;
let k' := mkChunk (ck_beg k) (ck_req k) CQuarantined in
modify (fun s => set_chunks (upd_chunk (st_chunks s) k') s) ;;
(if ck_n k' <=? kQuarantineMax then enqueue k' else recycle_chunk k') ;;
md
end
end.

(* ---------------------------------------------------------------------------- *)
(* The intermediate invariant: WfP_cf without wfc_compl0. Free's own steps break *)
(* Compl0 between a pop and the cache_dealloc that returns the record, so cdef is *)
(* tracked separately, as cgif's x-posts do.                                      *)
Section WFR.
Variable U : Univ.
Record WfR_cf (pp cc bb : Z) (s : astate) : Prop := {
wfr_len_regions : length (st_regions s) = 32%nat;
wfr_len_cache : length (st_cache s) = 32%nat;
wfr_reg0 : reg s 0 = region0;
wfr_classes : forall c, 1 <= c <= 31 -> wf_class_cf s c;
wfr_chunks : Forall (chunk_ok_cf s) (st_chunks s);
wfr_chunks_nodup : NoDup (map ck_beg (st_chunks s));
wfr_chunks_ev : Z.of_nat (length (st_chunks s)) + cc <= st_nev s;
wfr_prim_ev : prim_user_mapped s + kUserMapSize * pp <= kUserMapSize * st_nev s;
wfr_live : blocks_bytes s <= LIVE_MAX;
wfr_quarantine : wf_quar s;
wfr_batches_ev : Z.of_nat (length (all_batches s)) + bb <= st_nev s;
wfr_secondary : wf_sec_cf s;
wfr_fakestack : wf_fs s;
wfr_depot : depot_fits U (st_depot s);
wfr_nev : 0 <= st_nev s;
wfr_slack : 0 <= pp /\ 0 <= cc /\ 0 <= bb;
wfr_qinited : all_batches s <> [] -> st_cache_inited s = true;
wfr_secs_ev : Z.of_nat (length (st_secs s)) + cc <= st_nev s;
wfr_sec_live : Z.of_nat (length (st_sec_arr s)) <= cf_sec_live_max;
wfr_qsize : Forall (fun k => ck_n k <= kQuarantineMax) (q_items s)
}.
End WFR.

Lemma WfR_of_WfP_cf : forall U pp cc bb s, WfP_cf U pp cc bb s -> WfR_cf U pp cc bb s.
Proof. intros U pp cc bb s W. destruct W. constructor; assumption. Qed.
Lemma WfP_of_WfR_cf : forall U pp cc bb s, WfR_cf U pp cc bb s -> Compl0 s -> WfP_cf U pp cc bb s.
Proof. intros U pp cc bb s W HC. destruct W. constructor; assumption. Qed.

Ltac wfr_fields_y3 W :=
pose proof (wfr_len_regions _ _ _ _ _ W) as Xlr; pose proof (wfr_len_cache _ _ _ _ _ W) as Xlc;
pose proof (wfr_reg0 _ _ _ _ _ W) as Xr0; pose proof (wfr_classes _ _ _ _ _ W) as Xcl;
pose proof (wfr_chunks _ _ _ _ _ W) as Xck; pose proof (wfr_chunks_nodup _ _ _ _ _ W) as Xnd;
pose proof (wfr_chunks_ev _ _ _ _ _ W) as Xcev; pose proof (wfr_prim_ev _ _ _ _ _ W) as Xpev;
pose proof (wfr_live _ _ _ _ _ W) as Xlive; pose proof (wfr_quarantine _ _ _ _ _ W) as Xq;
pose proof (wfr_batches_ev _ _ _ _ _ W) as Xbev; pose proof (wfr_secondary _ _ _ _ _ W) as Xsec;
pose proof (wfr_fakestack _ _ _ _ _ W) as Xfs; pose proof (wfr_depot _ _ _ _ _ W) as Xdep;
pose proof (wfr_nev _ _ _ _ _ W) as Xnev; pose proof (wfr_slack _ _ _ _ _ W) as Xsl;
pose proof (wfr_qinited _ _ _ _ _ W) as Xqi; pose proof (wfr_secs_ev _ _ _ _ _ W) as Xsev;
pose proof (wfr_sec_live _ _ _ _ _ W) as Xslv; pose proof (wfr_qsize _ _ _ _ _ W) as Xqs.
Ltac sec_fields_cf X :=
pose proof (wsc_nodup _ X) as Snd; pose proof (wsc_arr_chunks _ X) as Sac; pose proof (wsc_arr_live _ X) as Sal;
pose proof (wsc_reserved _ X) as Sres; pose proof (wsc_reserved_al _ X) as Sral; pose proof (wsc_lens _ X) as Slen.
Ltac wfr_easy_y3 :=
first [ assumption
| match goal with H : wf_quar ?s0 |- wf_quar _ => apply (wf_quar_ext s0); [reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : Forall (fun k => ck_n k <= kQuarantineMax) (q_items ?s0) |- Forall (fun k => ck_n k <= kQuarantineMax) (q_items _) =>
apply (qsize_ext s0); [reflexivity | reflexivity | exact H] end
| match goal with H : wf_sec_cf ?s0 |- wf_sec_cf _ => apply (wf_sec_cf_ext s0); [reflexivity | reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : wf_fs ?s0 |- wf_fs _ => apply (wf_fs_ext s0); [reflexivity | exact H] end
| match goal with H : all_batches ?s0 <> [] -> st_cache_inited ?s0 = true |- all_batches _ <> [] -> st_cache_inited _ = true =>
first [ exact H | (intros ?HB; apply H; exact HB) ] end
| match goal with |- Z.of_nat (length (st_secs _)) + _ <= st_nev _ =>
solve [ cbn [st_secs st_nev set_chunks set_depot set_regions set_cache set_qthread set_qglobal set_nev set_sec_arr set_sec_reserved
set_cache_inited set_internal_inited set_fs]; lia ] end
| match goal with |- Z.of_nat (length (st_sec_arr _)) <= cf_sec_live_max =>
solve [ cbn [st_sec_arr set_chunks set_depot set_regions set_cache set_qthread set_qglobal set_nev set_secs set_sec_reserved
set_cache_inited set_internal_inited set_fs]; lia ] end
| idtac ].

Lemma Forall_chunk_ok_cf_ext : forall s s' l, st_secs s' = st_secs s -> Forall (chunk_ok_cf s) l -> Forall (chunk_ok_cf s') l.
Proof. intros s s' l E H. eapply Forall_impl; [|exact H]. intros k. apply chunk_ok_cf_ext. exact E. Qed.
Lemma WfR_len_regions_cf : forall U pp cc bb s c, WfR_cf U pp cc bb s -> 0 <= c <= 31 -> (Z.to_nat c < length (st_regions s))%nat.
Proof. intros U pp cc bb s c W Hc. rewrite (wfr_len_regions _ _ _ _ _ W). lia. Qed.
Lemma WfR_len_cache_cf : forall U pp cc bb s c, WfR_cf U pp cc bb s -> 0 <= c <= 31 -> (Z.to_nat c < length (st_cache s))%nat.
Proof. intros U pp cc bb s c W Hc. rewrite (wfr_len_cache _ _ _ _ _ W). lia. Qed.
Lemma mapped_bound_r_cf : forall U pp cc bb s c, WfR_cf U pp cc bb s -> 1 <= c <= 31 -> rg_mapped_user (reg s c) <= kFreeArrayOffset.
Proof. intros U pp cc bb s c W Hc. exact (wrc_mapped_bound _ _ _ _ _ _ (wfr_classes _ _ _ _ _ W c Hc)). Qed.
Lemma WfR_weaken_cf : forall U pp cc bb pp' cc' bb' s,
WfR_cf U pp cc bb s -> 0 <= pp' <= pp -> 0 <= cc' <= cc -> 0 <= bb' <= bb -> WfR_cf U pp' cc' bb' s.
Proof.
intros U pp cc bb pp' cc' bb' s W H1 H2 H3. wfr_fields_y3 W. constructor; wfr_easy_y3; unfold kUserMapSize in *; try lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* The event step, the cf form of YG02.v:153-166 with no side condition: the     *)
(* event fields are lower bounds on st_nev.                                      *)
Lemma WfP_cf_tick_y3 : forall U s, Wf_cf U s -> WfP_cf U 1 1 1 (set_nev (st_nev s + 1) s).
Proof.
intros U s W. unfold Wf_cf in W. apply WfP_of_WfR_cf.
2:{ intros c Hc. exact (wfc_compl0 _ _ _ _ _ W c Hc). }
pose proof (WfR_of_WfP_cf _ _ _ _ _ W) as W'. wfr_fields_y3 W'. constructor; wfr_easy_y3.
- cbn. lia.
- change (prim_user_mapped s + kUserMapSize * 1 <= kUserMapSize * (st_nev s + 1)). lia.
- change (Z.of_nat (length (all_batches s)) + 1 <= st_nev s + 1). lia.
- cbn. lia.
- lia.
Qed.
Lemma WfP_cf_set_depot_y3 : forall U pp cc bb s d,
WfP_cf U pp cc bb s -> depot_fits U d -> WfP_cf U pp cc bb (set_depot d s).
Proof.
intros U pp cc bb s d W Hd. apply WfP_of_WfR_cf; [|exact (wfc_compl0 _ _ _ _ _ W)].
pose proof (WfR_of_WfP_cf _ _ _ _ _ W) as W'. wfr_fields_y3 W'. constructor; wfr_easy_y3.
Qed.

(* ---------------------------------------------------------------------------- *)
(* The class record, cls_ok_cf: the lemmas of YG02.v:225-251 and YG06.v:95-269.  *)
Lemma Forall_del_hole_cf : forall (P : Z * Z -> Prop) off l, Forall P l -> Forall P (del_hole off l).
Proof.
intros P off l H. unfold del_hole. apply Forall_forall. intros h Hh. apply filter_In in Hh as [Hh _].
exact (proj1 (Forall_forall _ _) H h Hh).
Qed.
Lemma cls_ok_repart_cf : forall c r p (i : bool) ko bo r' p' (i' : bool) ko' bo' extra,
cls_ok_cf c r p i ko bo ->
rg_mapped_user r' = rg_mapped_user r -> rg_alloc_user r' = rg_alloc_user r -> rg_mapped_fa r' = rg_mapped_fa r ->
rg_holes r' = rg_holes r ->
runs_ok (rg_free r') -> 4 * fa_len (rg_free r') <= rg_mapped_fa r ->
(if i' then pc_max p' = max_cached c /\ Z.of_nat (length (pc_chunks p')) <= max_cached c else p' = pclass0) ->
Permutation (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
(extra ++ fa_elems (class_size c) (rg_free r') ++ pc_chunks p' ++ ko' ++ bo') ->
cls_ok_cf c r' p' i' ko' bo'.
Proof.
intros c r p i ko bo r' p' i' ko' bo' extra C E1 E2 E3 E4 Hruns Hfl Hcache HP.
pose proof (wrc_alloc _ _ _ _ _ _ C). pose proof (wrc_mapped_al _ _ _ _ _ _ C). pose proof (wrc_alloc_al _ _ _ _ _ _ C).
pose proof (wrc_fa _ _ _ _ _ _ C). pose proof (wrc_fa_bound _ _ _ _ _ _ C). pose proof (wrc_holes _ _ _ _ _ _ C).
pose proof (wrc_carved _ _ _ _ _ _ C). pose proof (wrc_mapped_bound _ _ _ _ _ _ C).
constructor; rewrite ?E1, ?E2, ?E3, ?E4; try assumption.
- pose proof (Permutation_NoDup HP (wrc_nodup _ _ _ _ _ _ C)) as ND. apply NoDup_app_iff in ND as (_ & ND & _). exact ND.
- pose proof (Forall_Permutation _ _ _ HP (wrc_elems _ _ _ _ _ _ C)) as FA. apply Forall_app in FA as [_ FA]. exact FA.
Qed.
Lemma cls_ok_take_cf : forall c r p i ko bo x rest,
cls_ok_cf c r p i ko bo ->
Permutation (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) (x :: rest) ->
0 <= x < rg_alloc_user r /\ x mod class_size c = 0 /\ ~ In x rest /\ NoDup rest.
Proof.
intros c r p i ko bo x rest C HP.
pose proof (Permutation_NoDup HP (wrc_nodup _ _ _ _ _ _ C)) as ND. inversion ND; subst.
pose proof (Forall_Permutation _ _ _ HP (wrc_elems _ _ _ _ _ _ C)) as FA. inversion FA; subst. tauto.
Qed.
Lemma cls_ok_map_user_cf : forall c r p i ko bo,
cls_ok_cf c r p i ko bo -> rg_mapped_user r - rg_alloc_user r < kMaxSize ->
rg_mapped_user r + kUserMapSize <= kFreeArrayOffset ->
cls_ok_cf c (mkRegion (rg_mapped_user r + kUserMapSize) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(del_hole (rg_mapped_user r) (rg_holes r))) p i ko bo.
Proof.
intros c r p i ko bo C Hcv Hroom.
pose proof (wrc_alloc _ _ _ _ _ _ C). pose proof (wrc_mapped_al _ _ _ _ _ _ C). pose proof (wrc_fa _ _ _ _ _ _ C).
pose proof (wrc_fa_bound _ _ _ _ _ _ C). pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh Hnd].
constructor; cbnr; try (exact (wrc_alloc_al _ _ _ _ _ _ C)); try (exact (wrc_fa_len _ _ _ _ _ _ C)); try (exact (wrc_fa_bound _ _ _ _ _ _ C));
try (exact (wrc_runs _ _ _ _ _ _ C)); try (exact (wrc_nodup _ _ _ _ _ _ C)); try (exact (wrc_elems _ _ _ _ _ _ C)); try (exact (wrc_cache _ _ _ _ _ _ C)).
- unfold kUserMapSize in *. lia.
- unfold kUserMapSize, kMaxSize in *. lia.
- rewrite Z.add_mod, Z.mod_same by (unfold kUserMapSize; lia). rewrite H0. reflexivity.
- assumption.
- split; [|apply NoDup_del_hole; exact Hnd]. apply Forall_del_hole_cf. exact Hh.
- exact Hroom.
Qed.
Lemma cls_ok_map_fa_cf : forall c r p i ko bo fa',
cls_ok_cf c r p i ko bo ->
rg_mapped_fa r <= fa' -> fa' mod kFreeArrayMapSize = 0 -> fa' <= kFreeArrayMax ->
cls_ok_cf c (mkRegion (rg_mapped_user r) (rg_alloc_user r) fa' (rg_free r)
(del_hole (kFreeArrayOffset + rg_mapped_fa r) (rg_holes r))) p i ko bo.
Proof.
intros c r p i ko bo fa' C H1 H2 H3. pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh Hnd]. pose proof (wrc_fa _ _ _ _ _ _ C).
pose proof (wrc_fa_len _ _ _ _ _ _ C).
constructor; cbnr; try (exact (wrc_alloc _ _ _ _ _ _ C)); try (exact (wrc_carved _ _ _ _ _ _ C)); try (exact (wrc_mapped_al _ _ _ _ _ _ C));
try (exact (wrc_alloc_al _ _ _ _ _ _ C)); try (exact (wrc_runs _ _ _ _ _ _ C)); try (exact (wrc_nodup _ _ _ _ _ _ C));
try (exact (wrc_elems _ _ _ _ _ _ C)); try (exact (wrc_cache _ _ _ _ _ _ C)); try (exact (wrc_mapped_bound _ _ _ _ _ _ C)); try lia.
split; [|apply NoDup_del_hole; exact Hnd]. apply Forall_del_hole_cf. exact Hh.
Qed.
Lemma cls_ok_populate_cf : forall c r p i ko bo,
cls_ok_cf c r p i ko bo -> 0 < class_size c ->
let cnt := (rg_mapped_user r - rg_alloc_user r) / class_size c in
1 <= cnt -> 4 * (fa_len (rg_free r) + cnt) <= rg_mapped_fa r ->
cls_ok_cf c (mkRegion (rg_mapped_user r) (rg_alloc_user r + cnt * class_size c) (rg_mapped_fa r)
(FRun (rg_alloc_user r) cnt :: rg_free r) (rg_holes r)) p i ko bo.
Proof.
intros c r p i ko bo C Hsz cnt Hcnt Hfa.
pose proof (wrc_alloc _ _ _ _ _ _ C) as A. pose proof (wrc_alloc_al _ _ _ _ _ _ C) as Aal.
pose proof (wrc_nodup _ _ _ _ _ _ C) as ND. pose proof (wrc_elems _ _ _ _ _ _ C) as EL.
assert (Hdiv : cnt * class_size c <= rg_mapped_user r - rg_alloc_user r).
{ subst cnt. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (Hrem : rg_mapped_user r - rg_alloc_user r - cnt * class_size c < class_size c).
{ subst cnt. pose proof (Z.mod_pos_bound (rg_mapped_user r - rg_alloc_user r) (class_size c) Hsz).
pose proof (Z.div_mod (rg_mapped_user r - rg_alloc_user r) (class_size c) ltac:(lia)). nia. }
constructor; cbnr; try (exact (wrc_mapped_al _ _ _ _ _ _ C)); try (exact (wrc_fa _ _ _ _ _ _ C)); try (exact (wrc_fa_bound _ _ _ _ _ _ C));
try (exact (wrc_cache _ _ _ _ _ _ C)); try (exact (wrc_mapped_bound _ _ _ _ _ _ C)); try (exact (wrc_holes _ _ _ _ _ _ C)).
- nia.
- pose proof (wrc_carved _ _ _ _ _ _ C). unfold kUserMapSize, kMaxSize in *. nia.
- rewrite Z.add_mod, Aal, Z_mod_mult by lia. reflexivity.
- cbn [fa_len]. lia.
- constructor; [lia | exact (wrc_runs _ _ _ _ _ _ C)].
- rewrite fa_elems_cons_run, <- app_assoc. apply NoDup_app_iff. split; [apply run_elems_NoDup; lia|]. split; [exact ND|].
intros x Hx Hy. apply In_run_elems in Hx as (j & Hj & ->).
pose proof (proj1 (Forall_forall _ _) EL _ Hy) as [B _]. nia.
- rewrite fa_elems_cons_run, <- app_assoc. apply Forall_app. split.
+ apply Forall_forall. intros x Hx. apply In_run_elems in Hx as (j & Hj & ->). split; [nia|].
rewrite Z.add_mod, Aal, Z_mod_mult by lia. reflexivity.
+ eapply Forall_impl; [|exact EL]. cbn beta. intros x [B M]. split; [nia | exact M].
Qed.
Lemma cls_ok_add_ko_cf : forall c r p i ko bo x,
cls_ok_cf c r p i ko bo ->
~ In x (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) ->
0 <= x < rg_alloc_user r -> x mod class_size c = 0 ->
cls_ok_cf c r p i (ko ++ [x]) bo.
Proof.
intros c r p i ko bo x C Hni Hx Hm.
assert (HP : Permutation (x :: fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
(fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ (ko ++ [x]) ++ bo)).
{ replace (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ (ko ++ [x]) ++ bo)
with ((fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko) ++ x :: bo) by (rewrite <- !app_assoc; reflexivity).
replace (x :: fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo)
with (x :: (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko) ++ bo) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_middle. }
constructor; try (exact (wrc_alloc _ _ _ _ _ _ C)); try (exact (wrc_carved _ _ _ _ _ _ C)); try (exact (wrc_mapped_al _ _ _ _ _ _ C)); try (exact (wrc_alloc_al _ _ _ _ _ _ C));
try (exact (wrc_fa _ _ _ _ _ _ C)); try (exact (wrc_fa_bound _ _ _ _ _ _ C)); try (exact (wrc_fa_len _ _ _ _ _ _ C));
try (exact (wrc_runs _ _ _ _ _ _ C)); try (exact (wrc_holes _ _ _ _ _ _ C)); try (exact (wrc_cache _ _ _ _ _ _ C)); try (exact (wrc_mapped_bound _ _ _ _ _ _ C)).
- eapply Permutation_NoDup; [exact HP|]. constructor; [exact Hni | exact (wrc_nodup _ _ _ _ _ _ C)].
- eapply Forall_Permutation; [exact HP|]. constructor; [split; [exact Hx | exact Hm] | exact (wrc_elems _ _ _ _ _ _ C)].
Qed.
Lemma fa_len_bound_y3 : forall c r p i ko bo,
cls_ok_cf c r p i ko bo -> 0 < class_size c -> class_size c * fa_len (rg_free r) <= rg_alloc_user r.
Proof.
intros c r p i ko bo C Hsz.
pose proof (wrc_nodup _ _ _ _ _ _ C) as ND. pose proof (wrc_elems _ _ _ _ _ _ C) as EL. pose proof (wrc_runs _ _ _ _ _ _ C) as R.
apply NoDup_app_iff in ND as (ND & _ & _). apply Forall_app in EL as [EL _].
rewrite <- (fa_elems_length (class_size c)) by exact R.
apply multiples_bound; [exact Hsz | pose proof (wrc_alloc _ _ _ _ _ _ C); lia | exact (wrc_alloc_al _ _ _ _ _ _ C) | exact ND | exact EL].
Qed.

(* ---------------------------------------------------------------------------- *)
(* The setters, YG02.v:173-224, YG02.v:272-293, YG06.v:487-524 over WfR_cf.       *)
Lemma WfR_set_region_y3 : forall U pp cc bb s c r' pp',
WfR_cf U pp cc bb s -> 1 <= c <= 31 ->
cls_ok_cf c r' (cache s c) (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
0 <= pp' ->
prim_user_mapped s - rg_mapped_user (reg s c) + rg_mapped_user r' + kUserMapSize * pp' <= kUserMapSize * st_nev s ->
WfR_cf U pp' cc bb (set_regions (zupd c r' (st_regions s)) s).
Proof.
intros U pp cc bb s c r' pp' W Hc Hcls Hpp' Hbound.
assert (Hlen : (Z.to_nat c < length (st_regions s))%nat) by (rewrite (wfr_len_regions _ _ _ _ _ W); lia).
wfr_fields_y3 W. constructor; wfr_easy_y3.
- cbn. rewrite zupd_length. assumption.
- rewrite reg_upd_other; [assumption | lia | lia | lia].
- intros c' Hc'. unfold wf_class_cf. rewrite cache_set_regions, chunk_offs_set_regions, batch_offs_set_regions. cbn [st_cache_inited set_regions].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite reg_upd_same; [exact Hcls | lia | exact Hlen].
+ rewrite reg_upd_other; [ | lia | lia | exact Hne]. exact (Xcl c' Hc').
- change (prim_user_mapped (set_regions (zupd c r' (st_regions s)) s) + kUserMapSize * pp' <= kUserMapSize * st_nev s).
rewrite prim_user_mapped_set_region; [| lia | exact Hlen]. exact Hbound.
- lia.
Qed.
Lemma WfR_set_pc_y3 : forall U pp cc bb s c p',
WfR_cf U pp cc bb s -> 1 <= c <= 31 ->
cls_ok_cf c (reg s c) p' (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
WfR_cf U pp cc bb (set_cache (zupd c p' (st_cache s)) s).
Proof.
intros U pp cc bb s c p' W Hc Hcls.
assert (Hlen : (Z.to_nat c < length (st_cache s))%nat) by (rewrite (wfr_len_cache _ _ _ _ _ W); lia).
wfr_fields_y3 W. constructor; wfr_easy_y3.
- cbn. rewrite zupd_length. assumption.
- intros c' Hc'. unfold wf_class_cf. rewrite reg_set_cache, chunk_offs_set_cache, batch_offs_set_cache. cbn [st_cache_inited set_cache].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite cache_upd_same; [exact Hcls | lia | exact Hlen].
+ rewrite cache_upd_other; [ | lia | lia | exact Hne]. exact (Xcl c' Hc').
Qed.
Lemma WfR_init_caches_cf : forall U pp cc bb s,
WfR_cf U pp cc bb s -> st_cache_inited s = false ->
WfR_cf U pp cc bb (set_cache_inited true (set_cache (init_caches (st_cache s)) s)).
Proof.
intros U pp cc bb s W Hi. wfr_fields_y3 W. constructor; wfr_easy_y3.
- cbn [st_cache set_cache_inited set_cache]. apply length_init_caches.
- intros c' Hc'. pose proof (Xcl c' Hc') as C. unfold wf_class_cf in *.
rewrite reg_set_cache_inited, reg_set_cache, chunk_offs_set_cache_inited, chunk_offs_set_cache,
batch_offs_set_cache_inited, batch_offs_set_cache, cache_after_init by lia.
cbn [st_cache_inited set_cache_inited]. rewrite Hi in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as Hp. cbn in Hp. rewrite Hp in C |- *. cbn [pc_chunks pclass0].
eapply (cls_ok_repart_cf c' _ _ false _ _ _ _ true _ _ []); try exact C; try reflexivity.
+ exact (wrc_runs _ _ _ _ _ _ C).
+ exact (wrc_fa_len _ _ _ _ _ _ C).
+ cbn [pc_max pc_chunks length Z.of_nat]. split; [reflexivity|]. pose proof (class_ok c' Hc'). lia.
- intros _. reflexivity.
Qed.
Lemma WfR_set_region_pc_y3 : forall U pp cc bb s c r' p' pp',
WfR_cf U pp cc bb s -> 1 <= c <= 31 ->
cls_ok_cf c r' p' (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
0 <= pp' ->
prim_user_mapped s - rg_mapped_user (reg s c) + rg_mapped_user r' + kUserMapSize * pp' <= kUserMapSize * st_nev s ->
WfR_cf U pp' cc bb (upd_pc c p' (upd_reg c r' s)).
Proof.
intros U pp cc bb s c r' p' pp' W Hc Hcls Hpp' Hbound.
assert (Hlen : (Z.to_nat c < length (st_regions s))%nat) by (rewrite (wfr_len_regions _ _ _ _ _ W); lia).
assert (Hlen' : (Z.to_nat c < length (st_cache s))%nat) by (rewrite (wfr_len_cache _ _ _ _ _ W); lia).
wfr_fields_y3 W. unfold upd_pc, upd_reg. constructor; wfr_easy_y3.
- cbn [st_regions set_cache set_regions]. rewrite zupd_length. assumption.
- cbn [st_cache st_regions set_cache set_regions]. rewrite zupd_length. assumption.
- unfold reg in *. cbn [st_regions set_cache set_regions]. rewrite znth_zupd_other; [assumption | lia | lia | lia].
- intros c' Hc'. unfold wf_class_cf in *. unfold reg, cache in *. cbn [st_regions st_cache st_cache_inited set_cache set_regions].
change (chunk_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (chunk_offs s c').
change (batch_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (batch_offs s c').
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite !znth_zupd_same; [exact Hcls | lia | exact Hlen' | lia | exact Hlen].
+ rewrite !znth_zupd_other; [ exact (Xcl c' Hc') | lia | lia | exact Hne | lia | lia | exact Hne].
- change (prim_user_mapped (set_regions (zupd c r' (st_regions s)) s) + kUserMapSize * pp' <= kUserMapSize * st_nev s).
rewrite prim_user_mapped_set_region; [| lia | exact Hlen]. exact Hbound.
- lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* The free-array push and the batch-class allocation, YG06.v:145-801 over       *)
(* WfR_cf. ensure_free_array keeps both arms: a grant grows rg_mapped_fa and      *)
(* keeps wrc_fa_len; a refusal is a spin (ns = false) when sof = true.           *)
Definition ensure_post_y3 (U : Univ) (pp cc bb : Z) (s : astate) (c need : Z) (sof : bool) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfR_cf U pp cc bb s' /\
rg_mapped_user r' = rg_mapped_user (reg s c) /\ rg_alloc_user r' = rg_alloc_user (reg s c) /\
rg_free r' = rg_free (reg s c) /\ rg_mapped_fa (reg s c) <= rg_mapped_fa r' /\
(ok = true -> 4 * need <= rg_mapped_fa r') /\ (ok = false -> ns = false /\ sof = false).
Lemma ensure_free_array_ok_y3 : forall U pp cc bb s c need sof ns,
WfR_cf U pp cc bb s -> 1 <= c <= 31 ->
fa_len (rg_free (reg s c)) <= need ->
4 * need <= rg_mapped_fa (reg s c) + kFreeArrayMapSize ->
4 * need <= kFreeArrayMax ->
atok ns (ensure_free_array c need sof s) (ensure_post_y3 U pp cc bb s c need sof).
Proof.
intros U pp cc bb s c need sof ns W Hc Hlen Hneed Hneed2.
pose proof (wfr_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_fa _ _ _ _ _ _ C) as [F0 Fal]. pose proof (wrc_fa_bound _ _ _ _ _ _ C) as Fb.
pose proof (wfr_slack _ _ _ _ _ W) as SL.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfR_len_regions_cf; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
unfold ensure_free_array. apply atok_bind. apply atok_get_region. cbn [fst snd].
destruct (Z.leb_spec (4 * need) (rg_mapped_fa (reg s c))) as [Hle|Hgt].
- apply atok_ret. exists (reg s c). rewrite ES. splits; auto; try lia.
- set (fa := rg_mapped_fa (reg s c)) in *.
assert (RU : round_up (4 * need) kFreeArrayMapSize = fa + kFreeArrayMapSize).
{ apply round_up_step; [unfold kFreeArrayMapSize; lia | exact Fal | lia]. }
assert (B29 : fa + kFreeArrayMapSize <= kFreeArrayMax).
{ apply Z.mod_divide in Fal as [q Hq]; [|unfold kFreeArrayMapSize; lia]. unfold kFreeArrayMax, kFreeArrayMapSize in *. nia. }
apply atok_bind. apply atok_mcheck; [apply Z.leb_le; rewrite RU; exact B29|].
cbn [fst snd]. apply atok_bind. apply atok_askz.
{ cbn [areq_ok]. rewrite RU. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Fal|]. split; [lia|].
pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh _]. eapply Forall_impl; [|exact Hh]. intros h ->. cbn [fst snd].
right; left. unfold EXH_HOLE, kFreeArrayOffset. lia. }
intros z Hz. cbn [fst snd].
assert (K : forall s1 r1, s1 = upd_reg c r1 s -> WfR_cf U pp cc bb s1 ->
rg_mapped_user r1 = rg_mapped_user (reg s c) -> rg_alloc_user r1 = rg_alloc_user (reg s c) ->
rg_free r1 = rg_free (reg s c) -> rg_mapped_fa r1 = fa -> aGranted z = false ->
atok (z =? 1) ((if sof then spin 213516 else ret false) s1) (ensure_post_y3 U pp cc bb s c need sof)).
{ intros s1 r1 -> W1 E1 E2 E3 E4 Eg'. unfold aGranted in Eg'. rewrite Eg'.
destruct sof; [apply atok_spin|]. apply atok_ret. exists r1. splits; auto; try lia. }
cbn [progz]. destruct (aGranted z) eqn:Eg.
+ apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. split; [reflexivity|]. rewrite RU.
split; [| cbnr; splits; try reflexivity; try lia; intros; discriminate].
eapply WfR_set_region_y3; [exact W | exact Hc | | lia | pose proof (wfr_prim_ev _ _ _ _ _ W); cbnr; lia].
apply cls_ok_map_fa_cf; [exact C | lia | | ].
* rewrite Z.add_mod, Fal, Z.mod_same by (unfold kFreeArrayMapSize; lia). reflexivity.
* exact B29.
+ apply atok_bind. replace (aDestroyed z) with false by (unfold aDestroyed; destruct Hz as [-> | ->]; reflexivity).
apply atok_ret. cbn [fst snd]. eapply (K s (reg s c)); try reflexivity; [symmetry; exact ES | exact W].
Qed.
Definition map_post_y3 (U : Univ) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfR_cf U (pp - 1) cc bb s' /\
rg_alloc_user r' = rg_alloc_user (reg s c) /\ rg_free r' = rg_free (reg s c) /\ rg_mapped_fa r' = rg_mapped_fa (reg s c) /\
rg_mapped_user (reg s c) <= rg_mapped_user r' <= rg_mapped_user (reg s c) + kUserMapSize /\
(ok = true -> rg_alloc_user (reg s c) + need * class_size c <= rg_mapped_user r') /\ (ok = false -> ns = false).
Lemma map_more_user_ok_cf : forall U pp cc bb s c need ns,
WfR_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp ->
0 < need * class_size c <= kMaxSize ->
rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset ->
atok ns (map_more_user c need s) (map_post_y3 U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hneed Hroom.
pose proof (wfr_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_alloc _ _ _ _ _ _ C) as A. pose proof (wrc_mapped_al _ _ _ _ _ _ C) as Mal.
pose proof Hroom as MB. pose proof (wfr_slack _ _ _ _ _ W) as SL.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfR_len_regions_cf; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
assert (Wk : WfR_cf U (pp - 1) cc bb s) by (eapply WfR_weaken_cf; [exact W | lia | lia | lia]).
unfold map_more_user. apply atok_bind. apply atok_get_region. cbn [fst snd].
set (mapped := rg_mapped_user (reg s c)) in *. set (alloc := rg_alloc_user (reg s c)) in *.
destruct (Z.ltb_spec mapped (alloc + need * class_size c)) as [Hlt|Hge].
- assert (RU : round_up (alloc + need * class_size c - mapped) kUserMapSize = kUserMapSize).
{ rewrite <- (Z.add_0_l kUserMapSize) at 2. apply round_up_step; [unfold kUserMapSize; lia | reflexivity | unfold kUserMapSize, kMaxSize in *; lia]. }
rewrite RU. apply atok_bind. apply atok_mcheck.
{ apply Z.leb_le. exact Hroom. }
cbn [fst snd]. apply atok_bind. apply atok_askz.
{ cbn [areq_ok]. splits; try reflexivity; try lia; try exact Mal.
pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh _]. eapply Forall_impl; [|exact Hh]. intros h ->. cbn [fst snd].
right; left. unfold EXH_HOLE. lia. }
intros z Hz. cbn [fst snd progz]. unfold aGranted. destruct (Z.eqb_spec z 1) as [->|Hz1].
+ apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. split; [reflexivity|]. split; [| cbnr; splits; try reflexivity; unfold kUserMapSize, kMaxSize in *; try lia; intros; discriminate].
eapply WfR_set_region_y3; [exact W | exact Hc | apply cls_ok_map_user_cf; [exact C | unfold kMaxSize in *; lia | exact MB] | lia
| pose proof (wfr_prim_ev _ _ _ _ _ W); cbnr; unfold kUserMapSize in *; lia].
+ apply atok_bind. replace (aDestroyed z) with false by (unfold aDestroyed; destruct Hz as [-> | ->]; [reflexivity | exfalso; apply Hz1; reflexivity]).
apply atok_ret. cbn [fst snd]. apply atok_ret. exists (reg s c). rewrite ES.
splits; try reflexivity; try assumption; unfold kUserMapSize, kMaxSize in *; try lia.
- apply atok_ret. exists (reg s c). rewrite ES. splits; try reflexivity; try assumption; unfold kUserMapSize, kMaxSize in *; try lia.
Qed.
Definition carve_x_cf (s : astate) (c : Z) (r' : region) : Prop :=
rg_alloc_user r' - rg_alloc_user (reg s c) = class_size c * (fa_len (rg_free r') - fa_len (rg_free (reg s c))) /\
rg_mapped_fa (reg s c) <= rg_mapped_fa r' /\
fa_len (rg_free (reg s c)) <= fa_len (rg_free r').
Definition populate_postx_cf (U : Univ) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfR_cf U (pp - 1) cc bb s' /\
fa_len (rg_free (reg s c)) <= fa_len (rg_free r') /\
(ok = true -> fa_len (rg_free (reg s c)) + need <= fa_len (rg_free r')) /\ (ok = false -> ns = false) /\
carve_x_cf s c r'.
Lemma populate_okx_cf : forall U pp cc bb s c need ns,
WfR_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= need ->
need * class_size c <= kMaxSize ->
rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset ->
atok ns (populate c need s) (populate_postx_cf U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hneed Hnsz Hroom.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & _).
assert (K32' : 32 <= class_size c). { pose proof K32 as K. apply Z.mod_divide in K as [k Hk]; [nia | lia]. }
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfR_len_regions_cf; [exact W | lia]).
unfold populate. apply atok_bind.
eapply atok_mono; [|apply (map_more_user_ok_cf U pp cc bb s c need ns W Hc Hpp ltac:(nia) Hroom)].
intros ns1 [ok s1] (r1 & -> & W1 & A1 & F1 & M1 & MM & OK1 & NS1). cbn [fst snd].
destruct ok; cbn [negb].
2:{ apply atok_ret. exists r1. splits; [reflexivity | exact W1 | rewrite F1; lia | intros; discriminate | exact NS1 |].
unfold carve_x_cf. rewrite A1, F1, M1. pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ (wfr_classes _ _ _ _ _ W c Hc))). splits; lia. }
specialize (OK1 eq_refl).
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
pose proof (wfr_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class_cf in C1. rewrite reg_upd_reg in C1 by (lia || exact HL).
set (cnt := (rg_mapped_user r1 - rg_alloc_user r1) / class_size c).
assert (Hcnt1 : need <= cnt). { subst cnt. apply Z.div_le_lower_bound; [lia|]. rewrite A1. nia. }
assert (Hcnt2 : cnt * class_size c <= rg_mapped_user r1 - rg_alloc_user r1). { subst cnt. rewrite Z.mul_comm. apply Z.mul_div_le. lia. }
assert (Hcnt4 : cnt <= 10240).
{ pose proof (wrc_carved _ _ _ _ _ _ C1) as CV. unfold kUserMapSize, kMaxSize in *.
assert (Hd1 : cnt <= (262144 + 65536) / class_size c) by (subst cnt; apply Z.div_le_mono; lia).
assert (Hd2 : (262144 + 65536) / class_size c <= (262144 + 65536) / 32) by (apply Z.div_le_compat_l; lia).
change ((262144 + 65536) / 32) with 10240 in Hd2. lia. }
assert (Hcnt3 : 4 * cnt <= kUserMapSize - 4) by (unfold kUserMapSize; lia).
pose proof (fa_len_bound_y3 _ _ _ _ _ _ C1 Ksz) as FB. rewrite F1 in FB. rewrite A1 in FB. rewrite ?F1, ?A1.
apply atok_bind.
eapply atok_mono; [|apply (ensure_free_array_ok_y3 U (pp - 1) cc bb (upd_reg c r1 s) c (fa_len (rg_free (reg s c)) + cnt) false ns1 W1 Hc)].
2:{ rewrite reg_upd_reg by (lia || exact HL). rewrite F1. lia. }
2:{ rewrite reg_upd_reg by (lia || exact HL). pose proof (wrc_fa_len _ _ _ _ _ _ C1) as FL. rewrite F1 in FL. unfold kUserMapSize, kFreeArrayMapSize in *. lia. }
2:{ assert (H32a : 32 * fa_len (rg_free (reg s c)) <= class_size c * fa_len (rg_free (reg s c)))
by (apply Z.mul_le_mono_nonneg_r; [|lia]; pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ C1)); rewrite F1 in *; lia).
assert (H32b : 32 * cnt <= cnt * class_size c) by nia.
pose proof (wrc_mapped_bound _ _ _ _ _ _ C1) as MB. pose proof (wrc_alloc _ _ _ _ _ _ C1).
unfold kFreeArrayMax, kFreeArrayOffset in *. lia. }
intros ns2 [ok2 s2] (r2 & -> & W2 & M2 & A2 & F2 & FA2 & OK2 & NS2). cbn [fst snd]. rewrite upd_reg_upd_reg in *.
rewrite reg_upd_reg in M2, A2, F2, FA2 by (lia || exact HL).
destruct ok2; cbn [negb].
2:{ apply atok_ret. exists r2. splits; [reflexivity | exact W2 | rewrite F2, F1; lia | intros; discriminate | intros E; exact (proj1 (NS2 E)) |].
unfold carve_x_cf. rewrite A2, A1, F2, F1, <- M1. splits; lia. }
specialize (OK2 eq_refl).
assert (HL2 : (Z.to_nat c < length (st_regions (upd_reg c r2 s)))%nat) by (unfold upd_reg; cbn; rewrite zupd_length; exact HL).
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL2). cbn [fst snd].
apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. rewrite upd_reg_upd_reg. split; [reflexivity|].
pose proof (wfr_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class_cf in C2. rewrite reg_upd_reg in C2 by (lia || exact HL2).
assert (Ecnt : (rg_mapped_user r2 - rg_alloc_user r2) / class_size c = cnt) by (subst cnt; rewrite M2, A2; reflexivity).
split; [| unfold carve_x_cf; cbnr; rewrite F2, F1; cbn [fa_len]; split; [lia | split; [intros _; lia | split; [intros; discriminate | rewrite A2, A1, <- M1; splits; lia]]]].
match goal with |- WfR_cf _ _ _ _ (upd_reg c ?r3 s) =>
rewrite <- (upd_reg_upd_reg c r2 r3 s); unfold upd_reg at 1 end.
eapply (WfR_set_region_y3 U (pp - 1) cc bb (upd_reg c r2 s) c); [exact W2 | exact Hc | | lia | ].
- pose proof (cls_ok_populate_cf c r2 _ _ _ _ C2 Ksz) as CP. cbn beta in CP. rewrite Ecnt in CP.
apply CP; [lia|]. rewrite F2, F1. lia.
- rewrite reg_upd_reg by (lia || exact HL2). cbnr. pose proof (wfr_prim_ev _ _ _ _ _ W2) as PE. unfold kUserMapSize in *. lia.
Qed.
Definition gfa_postx_cf (U : Univ) (pp cc bb : Z) (s : astate) (c n : Z) (ns : bool) (res : option (list Z) * astate) : Prop :=
let (o, s') := res in
match o with
| None => exists r', s' = upd_reg c r' s /\ WfR_cf U (pp - 1) cc bb s' /\ ns = false /\ carve_x_cf s c r'
| Some tops => exists r2 rest,
carve_x_cf s c r2 /\
WfR_cf U (pp - 1) cc bb (upd_reg c r2 s) /\
s' = upd_reg c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)) s /\
runs_ok rest /\ fa_elems (class_size c) (rg_free r2) = tops ++ fa_elems (class_size c) rest /\
Z.of_nat (length tops) = n /\ fa_len rest = fa_len (rg_free r2) - n
end.
Lemma get_from_allocator_okx_cf : forall U pp cc bb s c n ns,
WfR_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp -> 1 <= n -> n * class_size c <= kMaxSize -> n <= 8 ->
(fa_len (rg_free (reg s c)) < n -> rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset) ->
atok ns (get_from_allocator c n s) (gfa_postx_cf U pp cc bb s c n).
Proof.
intros U pp cc bb s c n ns W Hc Hpp Hn Hnsz Hn8 Hroom.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfR_len_regions_cf; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
pose proof (class_ok c Hc) as (Ksz & _).
pose proof (wfr_classes _ _ _ _ _ W c Hc) as C0. unfold wf_class_cf in C0.
pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ C0)) as FL0.
unfold get_from_allocator. apply atok_bind. apply atok_get_region. cbn [fst snd].
apply atok_bind.
apply (atok_mono _ _ (fun ns1 (res : bool * astate) => let (ok, s1) := res in exists r1, s1 = upd_reg c r1 s /\ WfR_cf U (pp - 1) cc bb s1 /\
(ok = true -> n <= fa_len (rg_free r1)) /\ (ok = false -> ns1 = false) /\ carve_x_cf s c r1)).
2:{ destruct (Z.ltb_spec (fa_len (rg_free (reg s c))) n) as [Hlt|Hge].
- eapply atok_mono; [|apply (populate_okx_cf U pp cc bb s c (n - fa_len (rg_free (reg s c))) ns W Hc Hpp); [lia | nia | exact (Hroom Hlt)]].
intros ns1 [ok s1] (r1 & -> & W1 & F1 & OK1 & NS1 & CV1). exists r1. splits; [reflexivity | exact W1 | intros Hok; specialize (OK1 Hok); lia | exact NS1 | exact CV1].
- apply atok_ret. exists (reg s c). rewrite ES. pose proof (wfr_slack _ _ _ _ _ W). splits; [reflexivity | eapply WfR_weaken_cf; [exact W|lia|lia|lia] | intros _; lia | intros; discriminate | unfold carve_x_cf; splits; lia]. }
intros ns1 [ok s1] (r1 & -> & W1 & OK1 & NS1 & CV1). cbn [fst snd].
destruct ok; cbn [negb].
2:{ apply atok_ret. exists r1. splits; [reflexivity | exact W1 | exact (NS1 eq_refl) | exact CV1]. }
specialize (OK1 eq_refl).
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
destruct (Z.ltb_spec (fa_len (rg_free r1)) n) as [Hlt|_]; [lia|].
pose proof (wfr_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class_cf in C1. rewrite reg_upd_reg in C1 by (lia || exact HL).
pose proof (wrc_runs _ _ _ _ _ _ C1) as R1.
destruct (fa_pop_n_some 10000 (class_size c) n (rg_free r1) [] R1) as (tops & rest & Ep); [lia | change (Z.of_nat 10000) with 10000; lia |].
assert (Hn0 : 0 <= n) by lia.
rewrite Ep. destruct (fa_pop_n_spec _ _ _ _ _ _ _ R1 Hn0 Ep) as (E1 & E2 & E3 & E4). cbn [rev app length] in E1, E4.
apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
exists r1, rest. rewrite upd_reg_upd_reg. splits; auto.
Qed.
Lemma pop_ok_cf : forall U pp cc bb s c l,
WfR_cf U pp cc bb s -> 1 <= c <= 31 -> st_cache_inited s = true -> pc_chunks (cache s c) = l -> l <> [] ->
WfR_cf U pp cc bb (upd_pc c (mkPC (pc_max (cache s c)) (removelast l)) s) /\
0 <= last l 0 < rg_alloc_user (reg s c) /\ last l 0 mod class_size c = 0 /\
~ In (last l 0) (class_elems (upd_pc c (mkPC (pc_max (cache s c)) (removelast l)) s) c).
Proof.
intros U pp cc bb s c l W Hc Hi Hl Hne.
pose proof (wfr_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C. rewrite Hi in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as [PM PL].
assert (HP : Permutation (fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c)
([last l 0] ++ fa_elems (class_size c) (rg_free (reg s c)) ++ removelast l ++ chunk_offs s c ++ batch_offs s c)).
{ rewrite Hl. rewrite <- (removelast_app_last l 0 Hne) at 1. apply perm_cache_pop. }
assert (C' : cls_ok_cf c (reg s c) (mkPC (pc_max (cache s c)) (removelast l)) true (chunk_offs s c) (batch_offs s c)).
{ eapply (cls_ok_repart_cf c _ _ true _ _ _ _ true _ _ [last l 0]); try exact C; try reflexivity.
- exact (wrc_runs _ _ _ _ _ _ C).
- exact (wrc_fa_len _ _ _ _ _ _ C).
- cbn [pc_max pc_chunks]. split; [exact PM|]. rewrite removelast_length by exact Hne. rewrite Hl in PL. lia.
- exact HP. }
assert (HLc : (Z.to_nat c < length (st_cache s))%nat) by (eapply WfR_len_cache_cf; [exact W | lia]).
split.
- unfold upd_pc. eapply WfR_set_pc_y3; [exact W | exact Hc | rewrite Hi; exact C'].
- destruct (cls_ok_take_cf c _ _ _ _ _ _ _ C HP) as (X1 & X2 & X3 & _).
splits; [lia | lia | exact X2 |].
unfold class_elems. rewrite cache_upd_pc by (lia || exact HLc). cbn [pc_chunks].
change (reg (upd_pc c ?[p] s) c) with (reg s c). change (chunk_offs (upd_pc c ?[p] s) c) with (chunk_offs s c).
change (batch_offs (upd_pc c ?[p] s) c) with (batch_offs s c). exact X3.
Qed.
Definition cache_alloc_post_y3 (U : Univ) (pp cc bb : Z) (s : astate) (c : Z) (ns : bool) (res : option Z * astate) : Prop :=
let (o, s') := res in
WfR_cf U (pp - 1) cc bb s' /\ regs_only s s' /\ st_cache_inited s' = true /\
match o with
| None => ns = false
| Some off => exists x, off = region_off c + x /\ 0 <= x < 2 ^ 32 /\ x < rg_alloc_user (reg s' c) /\ x mod class_size c = 0 /\
~ In x (class_elems s' c)
end.
Definition cache_alloc_postx_cf (U : Univ) (pp cc bb : Z) (s : astate) (c : Z) (ns : bool) (res : option Z * astate) : Prop :=
cache_alloc_post_y3 U pp cc bb s c ns res /\
(forall c', 1 <= c' <= 31 -> cdef (snd res) c' = cdef s c' + (if c' =? c then match fst res with Some _ => class_size c | None => 0 end else 0)).
Lemma cache_alloc_okx_cf : forall U pp cc bb s c ns,
WfR_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp ->
rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset ->
atok ns (cache_alloc c s) (cache_alloc_postx_cf U pp cc bb s c).
Proof.
intros U pp cc bb s c ns W Hc Hpp Hroom.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs).
unfold cache_alloc. apply atok_bind. unfold init_cache_if_needed. apply atok_bind. apply atok_get. cbn [fst snd].
assert (STEP1 : forall s1, WfR_cf U pp cc bb s1 -> st_cache_inited s1 = true -> regs_only s s1 ->
st_regions s1 = st_regions s -> (forall c', 1 <= c' <= 31 -> cdef s1 c' = cdef s c') ->
atok ns ((refill_if_empty c ;; p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| z :: l0 => set_pc c (mkPC (pc_max p) (removelast (z :: l0))) ;; ret (Some (region_off c + last (z :: l0) 0))
end) s1) (cache_alloc_postx_cf U pp cc bb s c)).
2:{ destruct (st_cache_inited s) eqn:Ei.
- apply atok_ret. apply (STEP1 s W Ei (regs_only_refl s) eq_refl). intros; reflexivity.
- apply atok_put. apply STEP1; [apply WfR_init_caches_cf; [exact W | exact Ei] | reflexivity | unfold regs_only; cbn; repeat split; reflexivity | reflexivity |].
intros c' Hc'. cbn [fst snd]. apply cdef_ext; [reflexivity|]. unfold class_elems. rewrite (cache_after_init s c' ltac:(lia)). reflexivity. }
intros s1 W1 Hi1 RO1 ER1 DEF1.
assert (HL : (Z.to_nat c < length (st_regions s1))%nat) by (eapply WfR_len_regions_cf; [exact W1 | lia]).
assert (HLc : (Z.to_nat c < length (st_cache s1))%nat) by (eapply WfR_len_cache_cf; [exact W1 | lia]).
pose proof (wfr_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class_cf in C1. rewrite Hi1 in C1.
pose proof (wrc_cache _ _ _ _ _ _ C1) as [PM1 PL1].
assert (REG1 : forall c', reg s1 c' = reg s c') by (intros c'; unfold reg; rewrite ER1; reflexivity).
assert (POP : forall ns2 pp' s2, WfR_cf U pp' cc bb s2 -> pp - 1 <= pp' <= pp -> st_cache_inited s2 = true -> regs_only s s2 ->
(pc_chunks (cache s2 c) = [] -> ns2 = false) -> (forall c', 1 <= c' <= 31 -> cdef s2 c' = cdef s c') ->
atok ns2 ((p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| z :: l0 => set_pc c (mkPC (pc_max p) (removelast (z :: l0))) ;; ret (Some (region_off c + last (z :: l0) 0))
end) s2) (cache_alloc_postx_cf U pp cc bb s c)).
{ intros ns2 pp' s2 W2 Hpp' Hi2 RO2 HN2 DEF2. apply atok_bind. apply atok_get_pc. cbn [fst snd].
assert (HLc2 : (Z.to_nat c < length (st_cache s2))%nat) by (eapply WfR_len_cache_cf; [exact W2 | lia]).
destruct (pc_chunks (cache s2 c)) as [|o l] eqn:El.
- apply atok_ret. unfold cache_alloc_postx_cf. cbn [fst snd]. split.
+ cbn. split; [eapply WfR_weaken_cf; [exact W2 | lia | pose proof (wfr_slack _ _ _ _ _ W2); lia | pose proof (wfr_slack _ _ _ _ _ W2); lia] | split; [exact RO2 | split; [exact Hi2 | exact (HN2 eq_refl)]]].
+ intros c' Hc'. rewrite (DEF2 c' Hc'). destruct (c' =? c); lia.
- apply atok_bind. apply atok_set_pc. cbn [fst snd]. apply atok_ret.
destruct (pop_ok_cf U pp' cc bb s2 c (o :: l) W2 Hc Hi2 El ltac:(discriminate)) as (W3 & X1 & X2 & X3).
unfold cache_alloc_postx_cf. cbn [fst snd]. split.
+ cbn -[upd_pc Z.add Z.mul region_off last removelast Z.pow Z.lt Z.le cdef Z.eqb]. split; [|split; [|split]].
* eapply WfR_weaken_cf; [exact W3 | lia | pose proof (wfr_slack _ _ _ _ _ W2); lia | pose proof (wfr_slack _ _ _ _ _ W2); lia].
* unfold regs_only in *. unfold upd_pc. cbn. exact RO2.
* exact Hi2.
* exists (last (o :: l) 0). split; [reflexivity|].
pose proof (mapped_bound_r_cf U pp' cc bb s2 c W2 Hc). pose proof (wrc_alloc _ _ _ _ _ _ (wfr_classes _ _ _ _ _ W2 c Hc)).
change (reg (upd_pc c ?[p] s2) c) with (reg s2 c).
splits; [lia | unfold kFreeArrayOffset in *; lia | lia | exact X2 | exact X3].
+ intros c' Hc'. rewrite <- (DEF2 c' Hc'). unfold cdef. rewrite reg_upd_pc_m.
destruct (Z.eqb_spec c' c) as [->|Hne].
* unfold class_elems. rewrite cache_upd_pc by (lia || exact HLc2). cbn [pc_chunks].
rewrite reg_upd_pc_m, chunk_offs_upd_pc_m, batch_offs_upd_pc_m. rewrite El, !length_app.
rewrite (removelast_length (o :: l)) by discriminate. cbn [length]. lia.
* unfold class_elems. rewrite reg_upd_pc_m, chunk_offs_upd_pc_m, batch_offs_upd_pc_m. unfold upd_pc. rewrite cache_upd_other by lia. lia. }
apply atok_bind. unfold refill_if_empty. apply atok_bind. apply atok_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s1 c)) as [|o l] eqn:El.
- rewrite PM1. apply atok_bind.
assert (N1 : 1 <= max_cached c / 2) by (apply Z.div_le_lower_bound; lia).
assert (N8 : max_cached c / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (N3 : max_cached c / 2 <= max_cached c) by (apply Z.div_le_upper_bound; lia).
assert (ROOM1 : fa_len (rg_free (reg s1 c)) < max_cached c / 2 -> rg_mapped_user (reg s1 c) + kUserMapSize <= kFreeArrayOffset).
{ intros _. rewrite REG1. exact Hroom. }
eapply atok_mono; [|apply (get_from_allocator_okx_cf U pp cc bb s1 c (max_cached c / 2) ns W1 Hc Hpp); [exact N1 | exact Kmcs | exact N8 | exact ROOM1]].
intros ns1 [got s2] Hg. cbn [fst snd]. destruct got as [tops|].
+ destruct Hg as (r2 & rest & CV2 & W2 & -> & Hruns & Hel & Hlen & Hfl).
apply atok_set_pc. cbn [fst snd].
set (r' := mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)).
pose proof (wfr_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class_cf in C2.
rewrite reg_upd_reg in C2 by (lia || exact HL). change (cache (upd_reg c r2 s1) c) with (cache s1 c) in C2.
change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1) in C2. rewrite Hi1 in C2.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c) in C2. change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c) in C2.
assert (W3 : WfR_cf U (pp - 1) cc bb (upd_pc c (mkPC (max_cached c) (cache_fill_order tops)) (upd_reg c r' s1))).
{ rewrite <- (upd_reg_upd_reg c r2 r' s1).
eapply (WfR_set_region_pc_y3 U (pp - 1) cc bb (upd_reg c r2 s1) c); [exact W2 | exact Hc | | lia | ].
- change (st_cache_inited (upd_reg c r2 s1)) with (st_cache_inited s1). rewrite Hi1.
change (chunk_offs (upd_reg c r2 s1) c) with (chunk_offs s1 c). change (batch_offs (upd_reg c r2 s1) c) with (batch_offs s1 c).
eapply (cls_ok_repart_cf c r2 (cache s1 c) true _ _ r' _ true _ _ []); try exact C2; try reflexivity.
+ exact Hruns.
+ subst r'. cbnr. pose proof (wrc_fa_len _ _ _ _ _ _ C2). lia.
+ cbn [pc_max pc_chunks]. split; [reflexivity|]. unfold cache_fill_order. rewrite length_rev. lia.
+ subst r'. cbnr. rewrite Hel, El. unfold cache_fill_order. cbn [pc_chunks app].
pose proof (perm_cache_refill (fa_elems (class_size c) rest) [] (chunk_offs s1 c) (batch_offs s1 c) tops) as PP. cbn [app] in PP. exact PP.
- rewrite reg_upd_reg by (lia || exact HL). subst r'. cbnr. pose proof (wfr_prim_ev _ _ _ _ _ W2) as PE.
unfold kUserMapSize in *. lia. }
eapply (POP ns1 (pp - 1)); [exact W3 | lia | exact Hi1 | unfold regs_only in *; cbn; exact RO1 | |].
{ unfold upd_pc. rewrite cache_upd_same by (lia || (unfold upd_reg; cbn; exact HLc)). cbn [pc_chunks]. unfold cache_fill_order.
intros E. apply (f_equal (@length Z)) in E. rewrite length_rev in E. cbn in E. lia. }
{ destruct CV2 as (CV2 & _).
intros c' Hc'. rewrite <- (DEF1 c' Hc'). unfold cdef.
destruct (Z.eq_dec c' c) as [->|Hne].
- unfold class_elems. rewrite cache_upd_pc by (lia || exact HLc).
rewrite !reg_upd_pc_m, !reg_upd_reg by (lia || exact HL). rewrite chunk_offs_upd_pc_m, batch_offs_upd_pc_m, chunk_offs_upd_reg_m, batch_offs_upd_reg_m.
subst r'. cbn [rg_alloc_user rg_free pc_chunks]. unfold cache_fill_order. rewrite El, !length_app, length_rev. cbn [length].
pose proof (fa_elems_length (class_size c) _ (wrc_runs _ _ _ _ _ _ C2)) as L2. rewrite Hel, length_app, Nat2Z.inj_add in L2.
pose proof (fa_elems_length (class_size c) _ (wrc_runs _ _ _ _ _ _ C1)) as L1.
rewrite !Nat2Z.inj_add. nia.
- unfold class_elems. rewrite !reg_upd_pc_m, !reg_upd_reg_other by lia. rewrite chunk_offs_upd_pc_m, batch_offs_upd_pc_m, chunk_offs_upd_reg_m, batch_offs_upd_reg_m.
unfold upd_pc. rewrite cache_upd_other by lia. rewrite cache_upd_reg_m. reflexivity. }
+ destruct Hg as (r' & -> & W2 & NS & CV2). apply atok_ret.
pose proof (wfr_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class_cf in C2. rewrite reg_upd_reg in C2 by (lia || exact HL).
change (cache (upd_reg c r' s1) c) with (cache s1 c) in C2. change (st_cache_inited (upd_reg c r' s1)) with (st_cache_inited s1) in C2. rewrite Hi1 in C2.
change (chunk_offs (upd_reg c r' s1) c) with (chunk_offs s1 c) in C2. change (batch_offs (upd_reg c r' s1) c) with (batch_offs s1 c) in C2.
eapply (POP ns1 (pp - 1)); [exact W2 | pose proof (wfr_slack _ _ _ _ _ W2); lia | exact Hi1 | unfold regs_only in *; cbn; exact RO1 | intros _; exact NS |].
destruct CV2 as (CV2 & _).
intros c' Hc'. cbn [fst snd]. rewrite <- (DEF1 c' Hc'). unfold cdef. destruct (Z.eq_dec c' c) as [->|Hne].
* unfold class_elems. rewrite !reg_upd_reg by (lia || exact HL). rewrite cache_upd_reg_m, chunk_offs_upd_reg_m, batch_offs_upd_reg_m.
pose proof (fa_elems_length (class_size c) _ (wrc_runs _ _ _ _ _ _ C2)) as L2. pose proof (fa_elems_length (class_size c) _ (wrc_runs _ _ _ _ _ _ C1)) as L1.
rewrite !length_app, !Nat2Z.inj_add. nia.
* unfold class_elems. rewrite !reg_upd_reg_other by lia. reflexivity.
- apply atok_ret. eapply (POP ns pp); [exact W1 | pose proof (wfr_slack _ _ _ _ _ W1); lia | exact Hi1 | exact RO1 | cbn [fst snd]; intros E; rewrite E in El; discriminate | exact DEF1].
Qed.

(* ---------------------------------------------------------------------------- *)
(* The primary-chunk geometry, YG07.v:155-195 over WfR_cf: the offset bound is   *)
(* wrc_mapped_bound's kFreeArrayOffset, not 2 ^ 31.                              *)
Lemma prim_chunk_off_y3 : forall U pp cc bb s k off, WfR_cf U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim off ->
let c := prim_class off in
1 <= c <= 30 /\ c = chunk_class (ck_req k) /\ from_primary (ck_req k) = true /\ 0 <= ck_req k /\
0 <= off - region_off c < kFreeArrayOffset /\ (off - region_off c) mod class_size c = 0.
Proof.
intros U pp cc bb s k off W Hk Hb c.
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k Hk) as [CKn CK]. rewrite Hb in CK. destruct CK as (CKp & CKc & CKo).
pose proof (primary_geometry (ck_req k) ltac:(lia) CKp) as (Gc & _).
assert (Hc : 1 <= c <= 30) by (subst c; rewrite CKc; exact Gc).
pose proof (In_chunk_offs s k off Hk Hb) as Hin. fold c in Hin.
pose proof (wfr_classes _ _ _ _ _ W c ltac:(lia)) as CL.
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) (off - region_off c)) as E.
specialize (E ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hin)).
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_bound_r_cf U pp cc bb s c W ltac:(lia)) as MB.
cbv beta in E. destruct E as [E1 E2].
subst c. splits; try lia; try assumption.
all: unfold kFreeArrayOffset in *; lia.
Qed.
Lemma prim_user_inj_y3 : forall U pp cc bb s k boff c x n,
WfR_cf U pp cc bb s -> In k (st_chunks s) -> ck_beg k = PPrim boff ->
1 <= c <= 31 -> 0 <= x < kFreeArrayOffset -> x mod class_size c = 0 -> 0 <= n -> from_primary n = true -> chunk_class n = c ->
boff + ck_rz k = region_off c + x + rz_size n -> boff = region_off c + x.
Proof.
intros U pp cc bb s k boff c x n W Hk Hb Hc Hx Hxa Hn Hp Hcn E.
pose proof (prim_chunk_off_y3 U pp cc bb s k boff W Hk Hb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
remember (prim_class boff) as c' eqn:Ec'.
pose proof (rz_size_bounds n) as [Rn _]. pose proof (rz_size_bounds (ck_req k)) as [Rk _]. unfold ck_rz in E.
pose proof (primary_geometry n Hn Hp) as (_ & Sn & _ & _ & Pn). rewrite Hcn in Sn, Pn.
pose proof (primary_geometry (ck_req k) G4 G3) as (_ & Sk & _). rewrite <- G2 in Sk.
pose proof (req_size_bounds n Hn) as (_ & Qn & _). pose proof (req_size_bounds (ck_req k) G4) as (_ & Qk & _).
assert (Ec : c' = c).
{ pose proof (prim_class_region_off c' (boff - region_off c' + rz_size (ck_req k)) ltac:(lia) ltac:(unfold kFreeArrayOffset in *; lia)) as P1.
pose proof (prim_class_region_off c (x + rz_size n) ltac:(lia) ltac:(unfold kFreeArrayOffset in *; lia)) as P2.
replace (region_off c' + (boff - region_off c' + rz_size (ck_req k))) with (region_off c + (x + rz_size n)) in P1 by lia.
congruence. }
subst c'. rewrite Ec in *.
destruct (Z.eq_dec (boff - region_off c) x) as [Eyx|Ne]; [lia|]. exfalso.
assert (D : (boff - region_off c - x) mod class_size c = 0).
{ rewrite Zminus_mod, G6, Hxa. cbn. first [reflexivity | apply Z.mod_0_l; lia]. }
apply Z.mod_divide in D as [q Hq]; [|lia].
assert (Hq0 : q <> 0) by (intros ->; lia).
assert (Habs : class_size c <= Z.abs (boff - region_off c - x)) by nia. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* YG03.v, re-keyed.                                                             *)
Lemma chunk_offs_begs_cf : forall s s' c, map ck_beg (st_chunks s') = map ck_beg (st_chunks s) -> chunk_offs s' c = chunk_offs s c.
Proof.
intros s s' c H. unfold chunk_offs. remember (st_chunks s) as l eqn:El. remember (st_chunks s') as l' eqn:El'. clear El El'.
revert l' H. induction l as [|k t IH]; intros [|k0 t0] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hb Ht. cbn [flat_map]. rewrite Hb, (IH _ Ht). reflexivity.
Qed.
Lemma sec_live_bytes_begs_cf : forall l l', map ck_beg l' = map ck_beg l -> map ck_req l' = map ck_req l ->
fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l'
= fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l.
Proof.
induction l as [|k t IH]; intros [|k0 t0] H1 H2; cbn in *; try discriminate; [reflexivity|].
injection H1 as Hb Ht. injection H2 as Hr Ht2. rewrite Hb, Hr, (IH _ Ht Ht2). reflexivity.
Qed.
Lemma user_inj_cf : forall U pp cc bb s k1 k2,
WfR_cf U pp cc bb s -> In k1 (st_chunks s) -> In k2 (st_chunks s) -> ck_user k1 = ck_user k2 -> k1 = k2.
Proof.
intros U pp cc bb s k1 k2 W H1 H2 E.
assert (EB : ck_beg k1 = ck_beg k2).
{ pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k1 H1) as [N1 C1].
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k2 H2) as [N2 C2].
unfold ck_user in E. destruct (ck_beg k1) as [|b1|r1 o1|c1 p1] eqn:E1; destruct (ck_beg k2) as [|b2|r2 o2|c2 p2] eqn:E2;
cbn [padd] in E; try discriminate; try solve [destruct C1 | destruct C2].
- injection E as E. destruct C2 as (P2 & Q2 & R2).
pose proof (prim_chunk_off_y3 U pp cc bb s k2 b2 W H2 E2) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
pose proof (prim_user_inj_y3 U pp cc bb s k1 b1 (prim_class b2) (b2 - region_off (prim_class b2)) (ck_req k2) W H1 E1
ltac:(lia) G5 G6 ltac:(lia) P2 (eq_sym Q2)) as J.
unfold ck_rz in E, J. f_equal. specialize (J ltac:(lia)). lia.
- injection E as <- Eo. destruct C1 as (_ & -> & _), C2 as (_ & -> & _). reflexivity. }
pose proof (In_split_beg _ _ H1 (wfr_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & El & N1 & N2).
rewrite El in H2. apply in_app_iff in H2 as [H2|[<-|H2]]; [exfalso | reflexivity | exfalso].
- apply N1. rewrite EB. apply in_map. exact H2.
- apply N2. rewrite EB. apply in_map. exact H2.
Qed.
Lemma find_user_block_cf : forall U pp cc bb s p n, WfR_cf U pp cc bb s -> In (p, n) (blocks s) ->
exists k, find_user (st_chunks s) p = Some k /\ In k (st_chunks s) /\ ck_state k = CAllocated /\ ck_user k = p /\ ck_req k = n.
Proof.
intros U pp cc bb s p n W Hin. apply In_blocks in Hin as (k & Hk & Hs & Hu & Hr).
destruct (find_user (st_chunks s) p) as [k'|] eqn:F.
- apply find_user_spec in F as [Hk' Hu']. pose proof (user_inj_cf U pp cc bb s k k' W Hk Hk' ltac:(congruence)) as <-.
exists k. auto.
- exfalso. exact (find_user_None _ _ F k Hk Hu).
Qed.
Lemma WfR_set_internal_inited_cf : forall U pp cc bb s v, WfR_cf U pp cc bb s -> WfR_cf U pp cc bb (set_internal_inited v s).
Proof. intros U pp cc bb s v W. wfr_fields_y3 W. constructor; wfr_easy_y3. Qed.
Definition quar_of_cf (k : chunk) : chunk := mkChunk (ck_beg k) (ck_req k) CQuarantined.
Definition bbytes_cf (l : list chunk) : Z := fold_right (fun k acc => if is_alloc k then ck_req k + acc else acc) 0 l.
Lemma blocks_bytes_eq_cf : forall s, blocks_bytes s = bbytes_cf (st_chunks s). Proof. reflexivity. Qed.
Lemma bbytes_split_cf : forall l1 k l2, bbytes_cf (l1 ++ k :: l2) = bbytes_cf (l1 ++ l2) + (if is_alloc k then ck_req k else 0).
Proof.
intros l1 k l2. unfold bbytes_cf. induction l1 as [|h t IH]; cbn; [destruct (is_alloc k); lia | rewrite IH; destruct (is_alloc h); lia].
Qed.
Lemma bbytes_app_cf : forall l1 l2, bbytes_cf (l1 ++ l2) = bbytes_cf l1 + bbytes_cf l2.
Proof. intros l1 l2. unfold bbytes_cf. induction l1 as [|h t IH]; cbn; [lia | rewrite IH; destruct (is_alloc h); lia]. Qed.
Lemma bbytes_nonneg_cf : forall s l, Forall (chunk_ok_cf s) l -> 0 <= bbytes_cf l.
Proof. intros s l H. unfold bbytes_cf. induction H as [|k t [Hk _] Ht IH]; cbn; [lia|]. destruct (is_alloc k); lia. Qed.
Lemma quar_nl_split_cf : forall l1 k l2, quar_nl (l1 ++ k :: l2) = quar_nl (l1 ++ l2) + (if is_alloc k then 0 else ck_n k).
Proof.
intros l1 k l2. unfold quar_nl. induction l1 as [|h t IH]; cbn; [destruct (is_alloc k); lia | rewrite IH; destruct (is_alloc h); lia].
Qed.
Lemma items_n_flat_app_cf : forall P Q, items_n (flat_map b_items (P ++ Q)) = items_n (flat_map b_items P) + items_n (flat_map b_items Q).
Proof. intros P Q. rewrite flat_map_app, items_n_app. reflexivity. Qed.
Lemma queued_n_eq_cf : forall s, queued_n s = items_n (flat_map b_items (qc_list (st_qthread s))) + items_n (flat_map b_items (qc_list (st_qglobal s))).
Proof. intros s. unfold queued_n, q_items, all_batches. apply items_n_flat_app_cf. Qed.
Lemma items_n_cons_cf : forall k l, items_n (k :: l) = ck_n k + items_n l. Proof. reflexivity. Qed.
Lemma items_n_nil_cf : items_n [] = 0. Proof. reflexivity. Qed.
Lemma unq_flip_cf : forall s l1 k l2, st_chunks s = l1 ++ k :: l2 -> ck_state k = CAllocated ->
unq_cf (set_chunks (l1 ++ quar_of_cf k :: l2) s) = unq_cf s + ck_n k.
Proof.
intros s l1 k l2 E Hst. unfold unq_cf, quar_n, queued_n, q_items, all_batches. cbn [st_chunks st_qthread st_qglobal set_chunks].
rewrite E, !quar_nl_split_cf. replace (is_alloc k) with true by (unfold is_alloc; rewrite Hst; reflexivity).
replace (is_alloc (quar_of_cf k)) with false by reflexivity. change (ck_n (quar_of_cf k)) with (ck_n k). lia.
Qed.
Lemma unq_push_cf : forall s s' kq nb,
st_chunks s' = st_chunks s -> st_qthread s' = qc_push (st_qthread s) kq nb -> st_qglobal s' = st_qglobal s ->
(nb = None -> need_new_batch (st_qthread s) = false) ->
unq_cf s' = unq_cf s - ck_n kq.
Proof.
intros s s' kq nb Hc Hq Hg Hnb. unfold unq_cf, quar_n. rewrite !queued_n_eq_cf, Hc, Hq, Hg.
enough (E : items_n (flat_map b_items (qc_list (qc_push (st_qthread s) kq nb))) = items_n (flat_map b_items (qc_list (st_qthread s))) + ck_n kq) by lia.
destruct nb as [off|]; cbn [qc_push qc_list].
- rewrite items_n_flat_app_cf. cbn [flat_map b_items app]. rewrite items_n_cons_cf, items_n_nil_cf. lia.
- specialize (Hnb eq_refl). unfold need_new_batch in Hnb. destruct (rev (qc_list (st_qthread s))) as [|lastb initr] eqn:R; [discriminate|].
rewrite <- (rev_involutive (qc_list (st_qthread s))). rewrite R. cbn [rev]. rewrite !items_n_flat_app_cf. cbn [flat_map b_items].
rewrite !app_nil_r, items_n_app, items_n_cons_cf, items_n_nil_cf. lia.
Qed.
Lemma unq_transfer_cf : forall s,
unq_cf (set_qglobal (mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s))) (set_qthread qc0 s)) = unq_cf s.
Proof.
intros s. unfold unq_cf, quar_n. rewrite !queued_n_eq_cf. cbn [st_chunks st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 flat_map].
rewrite items_n_nil_cf. fold (flat_map b_items (qc_list (st_qglobal s) ++ qc_list (st_qthread s))). rewrite items_n_flat_app_cf. lia.
Qed.
Lemma unq_pop_cf : forall s P rest bytes', qc_list (st_qglobal s) = P ++ rest ->
unq_cf (set_qglobal (mkQC rest bytes') s) = unq_cf s + items_n (flat_map b_items P).
Proof.
intros s P rest bytes' E. unfold unq_cf, quar_n. rewrite !queued_n_eq_cf. cbn [st_chunks st_qthread st_qglobal set_qglobal qc_list].
rewrite E, items_n_flat_app_cf. lia.
Qed.
Lemma unq_del_cf : forall s s' l1 k l2, st_chunks s = l1 ++ k :: l2 -> st_chunks s' = l1 ++ l2 -> ck_state k = CQuarantined ->
st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s -> unq_cf s' = unq_cf s - ck_n k.
Proof.
intros s s' l1 k l2 E E' Hst Hq Hg. unfold unq_cf, quar_n. rewrite !queued_n_eq_cf, E, E', Hq, Hg, quar_nl_split_cf.
replace (is_alloc k) with false by (unfold is_alloc; rewrite Hst; reflexivity). lia.
Qed.
Lemma unq_same_cf : forall s s', st_chunks s' = st_chunks s -> st_qthread s' = st_qthread s -> st_qglobal s' = st_qglobal s -> unq_cf s' = unq_cf s.
Proof. intros s s' H1 H2 H3. unfold unq_cf, quar_n. rewrite !queued_n_eq_cf, H1, H2, H3. reflexivity. Qed.
Lemma WfR_flip_cf : forall U pp cc bb s l1 k l2,
WfR_cf U pp cc bb s -> st_chunks s = l1 ++ k :: l2 -> ck_state k = CAllocated ->
WfR_cf U pp cc bb (set_chunks (l1 ++ quar_of_cf k :: l2) s).
Proof.
intros U pp cc bb s l1 k l2 W El Hst. wfr_fields_y3 W.
assert (EM : map ck_beg (l1 ++ quar_of_cf k :: l2) = map ck_beg (st_chunks s)) by (rewrite El, !map_app; reflexivity).
assert (ER : map ck_req (l1 ++ quar_of_cf k :: l2) = map ck_req (st_chunks s)) by (rewrite El, !map_app; reflexivity).
assert (ND : NoDup (map ck_beg (l1 ++ k :: l2))) by (rewrite <- El; exact Xnd).
rewrite map_app in ND. cbn in ND. apply NoDup_app_iff in ND as (ND1 & ND2 & ND3). inversion ND2; subst.
constructor; wfr_easy_y3.
- intros c Hc. unfold wf_class_cf. rewrite (chunk_offs_begs_cf s) by exact EM. rewrite batch_offs_set_chunks, reg_set_chunks, cache_set_chunks.
exact (Xcl c Hc).
- cbn [st_chunks set_chunks]. rewrite El in Xck. apply Forall_app in Xck as [X1 X2]. inversion X2; subst.
apply Forall_app. split; [eapply Forall_chunk_ok_cf_ext; [reflexivity | exact X1]|]. constructor; [|eapply Forall_chunk_ok_cf_ext; [reflexivity | eassumption]].
unfold chunk_ok_cf in *. cbn [quar_of_cf ck_req ck_beg st_secs set_chunks]. assumption.
- cbn [st_chunks set_chunks]. rewrite EM. exact Xnd.
- cbn [st_chunks set_chunks st_nev]. rewrite length_app in *. cbn [length] in *. rewrite El, length_app in Xcev. cbn in Xcev. lia.
- rewrite blocks_bytes_eq_cf in *. cbn [st_chunks set_chunks]. rewrite El in Xlive. rewrite bbytes_split_cf in *. cbn [is_alloc quar_of_cf ck_state].
rewrite El in Xck. apply Forall_app in Xck as [X1 X2]. inversion X2; subst.
match goal with H : chunk_ok_cf s k |- _ => destruct H as [Hn _] end. destruct (is_alloc k); lia.
- quar_fields Xq. constructor; cbn [st_qthread st_qglobal st_chunks set_chunks]; rewrite ?all_batches_set_chunks, ?q_items_set_chunks; try assumption.
eapply Forall_impl; [|exact Qit]. intros k' [Hk' Hs']. split; [|exact Hs'].
rewrite El in Hk'. apply in_app_iff in Hk' as [Hk'|[<-|Hk']]; [apply in_app_iff; left; exact Hk' | congruence | apply in_app_iff; right; right; exact Hk'].
- sec_fields_cf Xsec. constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks]; try assumption.
intros r. rewrite Sac. rewrite El. split; intros (k' & Hk' & Hb); apply in_app_iff in Hk' as [Hk'|[<-|Hk']].
+ exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb].
+ exists (quar_of_cf k). split; [apply in_app_iff; right; left; reflexivity | exact Hb].
+ exists k'. split; [apply in_app_iff; right; right; exact Hk' | exact Hb].
+ exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb].
+ exists k. split; [apply in_app_iff; right; left; reflexivity | exact Hb].
+ exists k'. split; [apply in_app_iff; right; right; exact Hk' | exact Hb].
Qed.
Lemma sum_bytes_app_cf : forall l1 l2, sum_bytes (l1 ++ l2) = sum_bytes l1 + sum_bytes l2.
Proof. intros l1 l2. unfold sum_bytes. apply (fold_right_add_app b_bytes). Qed.
Lemma b_bytes_app1_cf : forall b k, b_bytes (mkBatch (b_self b) (b_items b ++ [k])) = b_bytes b + ck_n k.
Proof.
intros b k. unfold b_bytes. cbn [b_items]. rewrite (fold_right_add_app ck_n). cbn [fold_right]. lia.
Qed.
Lemma cls_ok_rebatch_cf : forall c r p i ko bo ko' bo',
cls_ok_cf c r p i ko bo -> Permutation (ko ++ bo) (ko' ++ bo') -> cls_ok_cf c r p i ko' bo'.
Proof.
intros c r p i ko bo ko' bo' C HP.
eapply (cls_ok_repart_cf c r p i ko bo r p i ko' bo' []); try reflexivity; [exact C | exact (wrc_runs _ _ _ _ _ _ C) | exact (wrc_fa_len _ _ _ _ _ _ C) | exact (wrc_cache _ _ _ _ _ _ C) |].
cbn [app]. apply Permutation_app_head. apply Permutation_app_head. exact HP.
Qed.
Lemma cls_ok_add_bo_cf : forall c r p i ko bo x,
cls_ok_cf c r p i ko bo ->
~ In x (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) ->
0 <= x < rg_alloc_user r -> x mod class_size c = 0 ->
cls_ok_cf c r p i ko (bo ++ [x]).
Proof.
intros c r p i ko bo x C Hni Hx Hm.
pose proof (cls_ok_add_ko_cf c r p i ko bo x C Hni Hx Hm) as C'.
eapply cls_ok_rebatch_cf; [exact C'|]. rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma batch_offs_other_cf : forall s c, c <> kBatchClass -> batch_offs s c = [].
Proof. intros s c Hc. unfold batch_offs. destruct (Z.eqb_spec c kBatchClass); [lia | reflexivity]. Qed.
Lemma batch_offs_24_cf : forall s, batch_offs s kBatchClass = map (fun b => b_self b - region_off kBatchClass) (all_batches s).
Proof. intros s. unfold batch_offs. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma boffs_map_cf : forall L, map (fun b => b_self b - region_off kBatchClass) L = map (fun z => z - region_off kBatchClass) (map b_self L).
Proof. intros L. rewrite map_map. reflexivity. Qed.
Lemma qc_list_push_cf : forall q k nb,
(nb = None -> need_new_batch q = false) ->
exists T0 bl, qc_list (qc_push q k nb) = T0 ++ [bl] /\
match nb with
| Some off => T0 = qc_list q /\ bl = mkBatch off [k]
| None => exists lastb, qc_list q = T0 ++ [lastb] /\ bl = mkBatch (b_self lastb) (b_items lastb ++ [k]) /\
Z.of_nat (length (b_items lastb)) <> kBatchSlots
end /\
qc_bytes (qc_push q k nb) = qc_bytes q + ck_n k + (match nb with Some _ => kBatchBytes | None => 0 end).
Proof.
intros q k nb Hnb. destruct nb as [off|]; cbn -[ck_n kBatchBytes].
- exists (qc_list q), (mkBatch off [k]). splits; try reflexivity.
- specialize (Hnb eq_refl). unfold need_new_batch in Hnb.
destruct (rev (qc_list q)) as [|lastb initr] eqn:Er; [discriminate|].
exists (rev initr), (mkBatch (b_self lastb) (b_items lastb ++ [k])). splits; try reflexivity; [|lia].
exists lastb. splits; [|reflexivity | apply Z.eqb_neq; exact Hnb].
rewrite <- (rev_involutive (qc_list q)), Er. cbn. reflexivity.
Qed.
Lemma removelast_snoc_cf {X} : forall (l : list X) a, removelast (l ++ [a]) = l.
Proof.
intros l a. induction l as [|h t IH]; [reflexivity|]. cbn [app removelast]. rewrite IH.
destruct t as [|h' t']; cbn; reflexivity.
Qed.
Lemma need_new_batch_full_cf : forall q, need_new_batch q = true -> Forall bfull (removelast (qc_list q)) -> Forall bfull (qc_list q).
Proof.
intros q H F. unfold need_new_batch in H. destruct (rev (qc_list q)) as [|lastb initr] eqn:Er.
- apply (f_equal (@rev batch)) in Er. rewrite rev_involutive in Er. rewrite Er. constructor.
- apply (f_equal (@rev batch)) in Er. rewrite rev_involutive in Er. cbn [rev] in Er. rewrite Er in F |- *. rewrite removelast_snoc_cf in F.
apply Forall_app. split; [exact F|]. constructor; [|constructor]. unfold bfull. apply Z.eqb_eq in H. rewrite <- H. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma Forall_removelast_tl_cf {X} (P : X -> Prop) : forall a (l : list X), Forall P (removelast (a :: l)) -> Forall P (removelast l).
Proof. intros a l H. destruct l as [|b t]; [constructor|]. cbn [removelast] in H. inversion H; subst. assumption. Qed.
Lemma WfR_qpush_cf : forall U pp cc bb s kq nb,
WfR_cf U pp cc bb s -> 1 <= bb ->
In kq (st_chunks s) -> ck_state kq = CQuarantined -> ck_n kq <= kQuarantineMax -> ~ In (ck_beg kq) (map ck_beg (q_items s)) ->
match nb with
| Some off => exists x, off = region_off kBatchClass + x /\ 0 <= x < rg_alloc_user (reg s kBatchClass) /\
x mod class_size kBatchClass = 0 /\ ~ In x (class_elems s kBatchClass)
| None => need_new_batch (st_qthread s) = false
end ->
match nb with Some _ => st_cache_inited s = true | None => True end ->
(nb <> None -> need_new_batch (st_qthread s) = true) ->
WfR_cf U pp cc (bb - 1) (set_qthread (qc_push (st_qthread s) kq nb) s).
Proof.
intros U pp cc bb s kq nb W Hbb Hk Hst Hsz Hnotin Hnb Hci Hnew.
assert (QI' : all_batches s <> [] \/ st_cache_inited s = true).
{ destruct nb as [off|]; [right; exact Hci|]. left. unfold all_batches. intros E. apply app_eq_nil in E as [E _].
unfold need_new_batch in Hnb. rewrite E in Hnb. cbn in Hnb. discriminate. }
destruct (qc_list_push_cf (st_qthread s) kq nb ltac:(intros ->; exact Hnb)) as (T0 & bl & EL & CASE & EB).
set (q' := qc_push (st_qthread s) kq nb) in *.
wfr_fields_y3 W. quar_fields Xq.
assert (SHAPE : exists T1 its, qc_list (st_qthread s) = T0 ++ T1 /\ b_items bl = its ++ [kq] /\ flat_map b_items T1 = its /\
sum_bytes [bl] = sum_bytes T1 + ck_n kq + (match nb with Some _ => kBatchBytes | None => 0 end) /\
(1 <= length (b_items bl) <= Z.to_nat kBatchSlots)%nat /\
map b_self (T0 ++ [bl]) = map b_self (qc_list (st_qthread s)) ++ (match nb with Some off => [off] | None => [] end)).
{ destruct nb as [off|].
- destruct CASE as [-> ->]. exists [], []. rewrite app_nil_r, map_app. cbn -[ck_n kBatchBytes kBatchSlots Z.add Z.of_nat Z.to_nat].
unfold kBatchSlots. splits; try reflexivity; try lia. unfold b_bytes. cbn -[ck_n kBatchBytes Z.add]. lia.
- destruct CASE as (lastb & ET & -> & Hlen). exists [lastb], (b_items lastb). rewrite ET.
pose proof (proj1 (Forall_forall _ _) Qbat lastb ltac:(unfold all_batches; rewrite ET, <- app_assoc; apply in_elt)) as BL.
cbn -[ck_n kBatchBytes kBatchSlots b_bytes Z.add Z.of_nat Z.to_nat]. rewrite app_nil_r, b_bytes_app1_cf, !map_app. cbn [map b_self].
rewrite length_app. cbn [length]. unfold kBatchSlots in *. splits; try reflexivity; try lia. rewrite app_nil_r. reflexivity. }
destruct SHAPE as (T1 & its & ET & EI & EF & ES & BLEN & SELF).
assert (AB : all_batches (set_qthread q' s) = (T0 ++ [bl]) ++ qc_list (st_qglobal s)) by (unfold all_batches; cbn; rewrite EL; reflexivity).
assert (AB0 : all_batches s = (T0 ++ T1) ++ qc_list (st_qglobal s)) by (unfold all_batches; rewrite ET; reflexivity).
assert (QI : q_items (set_qthread q' s) = (flat_map b_items T0 ++ its ++ [kq]) ++ flat_map b_items (qc_list (st_qglobal s))).
{ unfold q_items. rewrite AB, !flat_map_app. cbn [flat_map]. rewrite EI, app_nil_r, app_assoc. reflexivity. }
assert (QI0 : q_items s = (flat_map b_items T0 ++ its) ++ flat_map b_items (qc_list (st_qglobal s))).
{ unfold q_items. rewrite AB0, !flat_map_app, EF. reflexivity. }
assert (PQ : Permutation (q_items (set_qthread q' s)) (kq :: q_items s)).
{ rewrite QI, QI0. rewrite !app_assoc. rewrite <- (app_assoc (flat_map b_items T0 ++ its) [kq]). cbn [app].
apply Permutation_sym. apply Permutation_middle. }
assert (PB : Permutation (batch_offs (set_qthread q' s) kBatchClass)
(batch_offs s kBatchClass ++ map (fun z => z - region_off kBatchClass) (match nb with Some off => [off] | None => [] end))).
{ rewrite !batch_offs_24_cf, !boffs_map_cf, AB, <- map_app. apply Permutation_map. unfold all_batches.
rewrite !map_app, <- (map_app b_self T0 [bl]), SELF, <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
constructor; wfr_easy_y3.
- intros c Hc. unfold wf_class_cf. cbn [st_cache_inited set_qthread]. change (reg (set_qthread q' s) c) with (reg s c). change (cache (set_qthread q' s) c) with (cache s c).
rewrite (chunk_offs_begs_cf s) by reflexivity.
pose proof (Xcl c Hc) as C. unfold wf_class_cf in C.
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
+ eapply cls_ok_rebatch_cf; [|apply Permutation_app_head; apply Permutation_sym; exact PB].
destruct nb as [off|]; [|rewrite app_nil_r; exact C].
destruct Hnb as (x & -> & Hx & Hxm & Hxni). cbn [map]. replace (region_off kBatchClass + x - region_off kBatchClass) with x by lia.
apply cls_ok_add_bo_cf; [exact C | exact Hxni | exact Hx | exact Hxm].
+ rewrite !batch_offs_other_cf by exact Hne. rewrite batch_offs_other_cf in C by exact Hne. exact C.
- constructor; cbn [st_qthread st_qglobal st_chunks set_qthread]; try assumption.
+ subst q'. rewrite EB, EL, sum_bytes_app_cf, ES. rewrite Qbt, ET, sum_bytes_app_cf. lia.
+ rewrite AB. rewrite AB0 in Qbat. rewrite <- app_assoc in Qbat |- *. apply Forall_app in Qbat as [Q1 Q2]. apply Forall_app in Q2 as [_ Q3].
apply Forall_app. split; [exact Q1|]. constructor; [exact BLEN | exact Q3].
+ eapply Forall_Permutation; [apply Permutation_sym; exact PQ|]. constructor; [split; assumption | exact Qit].
+ eapply NoDup_Permutation; [apply Permutation_map; apply Permutation_sym; exact PQ|]. cbn [map]. constructor; [exact Hnotin | exact Qnd].
+
rewrite EL, removelast_snoc_cf. destruct nb as [off|].
* destruct CASE as [-> _]. apply need_new_batch_full_cf; [apply Hnew; discriminate | exact Qtf].
* destruct CASE as (lastb & ET' & _ & _). rewrite ET', removelast_snoc_cf in Qtf. exact Qtf.
- cbn [st_nev set_qthread]. rewrite AB. rewrite AB0 in Xbev. rewrite !length_app in *. cbn [length] in *. lia.
- lia.
- cbn [st_cache_inited set_qthread]. intros _. destruct QI' as [Q|Q]; [exact (Xqi Q) | exact Q].
- (* wfr_qsize: the pushed item is within kQuarantineMax (free_cf's enqueue arm) *)
eapply Forall_Permutation; [apply Permutation_sym; exact PQ|]. constructor; [exact Hsz | exact Xqs].
Qed.
Definition enqueue_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (kq : chunk) (ns : bool) (res : unit * astate) : Prop :=
let s' := snd res in
WfR_cf U (pp - 1) cc (bb - 1) s' /\ st_chunks s' = st_chunks s /\ st_secs s' = st_secs s /\ st_sec_arr s' = st_sec_arr s /\
st_sec_reserved s' = st_sec_reserved s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\ st_nev s' = st_nev s /\
(exists nb, st_qthread s' = qc_push (st_qthread s) kq nb /\ (nb = None -> need_new_batch (st_qthread s) = false)) /\
st_qglobal s' = st_qglobal s.
Definition enqueue_postx_cf (U : Univ) (pp cc bb : Z) (s : astate) (kq : chunk) (ns : bool) (res : unit * astate) : Prop :=
enqueue_post_cf U pp cc bb s kq ns res /\
(forall c', 1 <= c' <= 31 -> cdef (snd res) c' = cdef s c').
Lemma length_qc_push_none_cf : forall q k, length (qc_list (qc_push q k None)) = length (qc_list q).
Proof.
intros q k. cbn [qc_push qc_list]. rewrite <- (length_rev (qc_list q)). destruct (rev (qc_list q)) as [|lastb initr]; [reflexivity|].
rewrite length_app, length_rev. cbn [length]. lia.
Qed.
Lemma enqueue_okx_cf : forall U pp cc bb s kq ns,
WfR_cf U pp cc bb s -> 1 <= pp -> 1 <= bb ->
In kq (st_chunks s) -> ck_state kq = CQuarantined -> ck_n kq <= kQuarantineMax -> ~ In (ck_beg kq) (map ck_beg (q_items s)) ->
rg_mapped_user (reg s kBatchClass) + kUserMapSize <= kFreeArrayOffset ->
atok ns (enqueue kq s) (enqueue_postx_cf U pp cc bb s kq).
Proof.
intros U pp cc bb s kq ns W Hpp Hbb Hk Hst Hsz Hni Hreg.
unfold enqueue. apply atok_bind. apply atok_get. cbn [fst snd]. apply atok_bind.
destruct (need_new_batch (st_qthread s)) eqn:NB.
- apply atok_bind. eapply atok_mono; [|apply (cache_alloc_okx_cf U pp cc bb s kBatchClass ns W ltac:(unfold kBatchClass; lia) Hpp Hreg)].
intros ns2 [o s2] ((W2 & RO2 & Hi2 & Ho) & DEF2). cbn [fst snd] in DEF2 |- *.
destruct RO2 as (Rck & Rsecs & Rarr & Rres & Rqt & Rqg & Rfs & Rdep & Rii & Rnev).
destruct o as [off|].
+ apply atok_ret. apply atok_modify. cbn [fst snd]. unfold enqueue_postx_cf. cbn [snd]. split.
* split; [|cbn; rewrite ?Rck, ?Rsecs, ?Rarr, ?Rres, ?Rfs, ?Rdep, ?Rnev, ?Rqt, ?Rqg; splits; try reflexivity; exists (Some off); split; [reflexivity | intros; discriminate]].
apply WfR_qpush_cf; [exact W2 | lia | rewrite Rck; exact Hk | exact Hst | exact Hsz | | | exact Hi2 | intros _; rewrite Rqt; exact NB].
-- unfold q_items, all_batches. rewrite Rqt, Rqg. exact Hni.
-- destruct Ho as (x & -> & Hx32 & Hxa & Hxm & Hxni). exists x. splits; auto; lia.
*
intros c' Hc'. rewrite <- (Z.add_0_r (cdef s c')).
replace 0 with ((if c' =? kBatchClass then class_size kBatchClass else 0) - (if c' =? kBatchClass then class_size kBatchClass else 0)) by lia.
rewrite Z.add_sub_assoc, <- (DEF2 c' Hc'). unfold cdef, class_elems.
change (reg (set_qthread ?[q] s2) c') with (reg s2 c'). change (cache (set_qthread ?[q] s2) c') with (cache s2 c').
change (chunk_offs (set_qthread ?[q] s2) c') with (chunk_offs s2 c').
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qthread qc_push qc_list].
destruct (Z.eqb_spec c' kBatchClass) as [->|Hne]; [|lia].
rewrite !length_app, !length_map, !length_app. cbn [length]. rewrite !Nat2Z.inj_add. lia.
+ subst ns2. apply atok_spin.
- apply atok_ret. cbn [fst snd]. apply atok_modify. cbn [fst snd]. unfold enqueue_postx_cf. cbn [snd]. split.
+ split; [|cbn; splits; try reflexivity; exists None; split; [reflexivity | intros _; exact NB]].
pose proof (wfr_slack _ _ _ _ _ W). apply (WfR_weaken_cf U pp cc (bb - 1)); [|lia|lia|lia].
apply WfR_qpush_cf; [exact W | lia | exact Hk | exact Hst | exact Hsz | exact Hni | exact NB | exact I | intros HNN; exfalso; apply HNN; reflexivity].
+ intros c' Hc'. apply cdef_ext; [reflexivity|]. unfold class_elems.
change (reg (set_qthread ?[q] s) c') with (reg s c'). change (cache (set_qthread ?[q] s) c') with (cache s c').
change (chunk_offs (set_qthread ?[q] s) c') with (chunk_offs s c').
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qthread].
destruct (c' =? kBatchClass); [|reflexivity]. rewrite !length_app, !length_map, !length_app, length_qc_push_none_cf. reflexivity.
Qed.
Lemma enqueue_ok_cf : forall U pp cc bb s kq ns,
WfR_cf U pp cc bb s -> 1 <= pp -> 1 <= bb ->
In kq (st_chunks s) -> ck_state kq = CQuarantined -> ck_n kq <= kQuarantineMax -> ~ In (ck_beg kq) (map ck_beg (q_items s)) ->
rg_mapped_user (reg s kBatchClass) + kUserMapSize <= kFreeArrayOffset ->
atok ns (enqueue kq s) (enqueue_post_cf U pp cc bb s kq).
Proof.
intros U pp cc bb s kq ns W Hpp Hbb Hk Hst Hsz Hni Hreg.
eapply atok_mono; [|exact (enqueue_okx_cf U pp cc bb s kq ns W Hpp Hbb Hk Hst Hsz Hni Hreg)]. intros b r (H & _). exact H.
Qed.
Lemma WfR_transfer_cf : forall U pp cc bb s,
WfR_cf U pp cc bb s ->
kQuarantineCacheMax < qc_bytes (st_qthread s) ->
let g := mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)) in
WfR_cf U pp cc bb (set_qglobal g (set_qthread qc0 s)).
Proof.
intros U pp cc bb s W Hover g. subst g. set (g := mkQC _ _).
wfr_fields_y3 W. quar_fields Xq.
assert (PB : Permutation (all_batches (set_qglobal g (set_qthread qc0 s))) (all_batches s)).
{ unfold all_batches. cbn. apply Permutation_app_comm. }
assert (PQ : Permutation (q_items (set_qglobal g (set_qthread qc0 s))) (q_items s)).
{ unfold q_items, all_batches in *. cbn in *. rewrite !flat_map_app. apply Permutation_app_comm. }
constructor; wfr_easy_y3.
- intros c Hc. unfold wf_class_cf. cbn [st_cache_inited set_qglobal set_qthread].
change (reg (set_qglobal g (set_qthread qc0 s)) c) with (reg s c). change (cache (set_qglobal g (set_qthread qc0 s)) c) with (cache s c).
rewrite (chunk_offs_begs_cf s) by reflexivity. pose proof (Xcl c Hc) as C. unfold wf_class_cf in C.
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
+ eapply cls_ok_rebatch_cf; [exact C|]. apply Permutation_app_head. rewrite !batch_offs_24_cf. apply Permutation_map. apply Permutation_sym. exact PB.
+ rewrite !batch_offs_other_cf in * by exact Hne. exact C.
- constructor; subst g; cbn [st_qthread st_qglobal st_chunks set_qglobal set_qthread qc0 qc_bytes qc_list]; try assumption.
+ reflexivity.
+ rewrite sum_bytes_app_cf. lia.
+ eapply Forall_Permutation; [apply Permutation_sym; exact PB | exact Qbat].
+ eapply Forall_Permutation; [apply Permutation_sym; exact PQ | exact Qit].
+ eapply NoDup_Permutation; [apply Permutation_map; apply Permutation_sym; exact PQ | exact Qnd].
+ constructor.
+
destruct Qgr as (F & GS & EG & FF & FG). exists F, (GS ++ [qc_list (st_qthread s)]).
rewrite EG, concat_app. cbn [concat]. rewrite app_nil_r, <- app_assoc. split; [reflexivity|]. split; [exact FF|].
apply Forall_app. split; [exact FG|]. constructor; [|constructor]. unfold qgroup_ok. rewrite <- Qbt. split; [|split; [exact Qtf | exact Hover]].
intros E. rewrite Qbt, E in Hover. cbn in Hover. unfold kQuarantineCacheMax in Hover. lia.
- cbn [st_nev set_qglobal set_qthread]. rewrite (Permutation_length PB). exact Xbev.
- cbn [st_cache_inited set_qglobal set_qthread]. intros NE. apply Xqi. intros E. apply NE.
apply Permutation_sym in PB. rewrite E in PB. apply Permutation_nil in PB. exact PB.
- (* wfr_qsize: the transfer moves the thread's items to the global queue *)
eapply Forall_Permutation; [apply Permutation_sym; exact PQ | exact Xqs].
Qed.
Lemma pop_batches_spec_cf : forall fuel q acc q' pop,
pop_batches fuel q acc = (q', pop) ->
exists P, pop = rev acc ++ P /\ qc_list q = P ++ qc_list q' /\ qc_bytes q' = qc_bytes q - sum_bytes P.
Proof.
induction fuel as [|f IH]; intros q acc q' pop H; cbn [pop_batches] in H.
- injection H as <- <-. exists []. rewrite !app_nil_r. cbn. splits; [reflexivity | reflexivity | lia].
- destruct (qc_bytes q <=? kQuarantineMin).
+ injection H as <- <-. exists []. rewrite !app_nil_r. cbn. splits; [reflexivity | reflexivity | lia].
+ remember (qc_list q) as L eqn:El. destruct L as [|b t].
* injection H as <- <-. exists []. cbn. splits; [rewrite app_nil_r; reflexivity | rewrite <- El; reflexivity | lia].
* apply IH in H as (P & -> & E2 & E3). cbn [qc_list qc_bytes] in E2, E3. exists (b :: P). cbn [rev]. rewrite <- app_assoc. cbn [app].
splits; [reflexivity | rewrite E2; reflexivity | unfold sum_bytes in *; cbn [fold_right]; lia].
Qed.
Lemma pop_batches_stop_cf : forall fuel q acc q' pop,
pop_batches fuel q acc = (q', pop) -> (length (qc_list q) < fuel)%nat ->
qc_bytes q' <= kQuarantineMin \/ qc_list q' = [].
Proof.
induction fuel as [|f IH]; intros q acc q' pop H Hlen; cbn [pop_batches] in H; [lia|].
destruct (Z.leb_spec (qc_bytes q) kQuarantineMin) as [Hle|Hgt].
- injection H as <- <-. left. exact Hle.
- destruct (qc_list q) as [|b t] eqn:El.
+ injection H as <- <-. right. exact El.
+ apply (IH _ _ _ _ H). cbn [qc_list]. cbn [length] in Hlen. lia.
Qed.
Definition RI_cf (U : Univ) (pp cc bb : Z) (s : astate) (P : list batch) : Prop :=
WfR_cf U pp cc bb s /\
Forall (fun k => In k (st_chunks s) /\ ck_state k = CQuarantined) (flat_map b_items P) /\
NoDup (map ck_beg (flat_map b_items P ++ q_items s)) /\
Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) P /\
Forall (fun b => 0 <= b_self b - region_off kBatchClass < rg_alloc_user (reg s kBatchClass) /\
(b_self b - region_off kBatchClass) mod class_size kBatchClass = 0 /\
~ In (b_self b - region_off kBatchClass) (class_elems s kBatchClass)) P /\
NoDup (map b_self P).
Lemma perm_insert4_cf : forall (F Pc K T P R : list Z),
Permutation (F ++ Pc ++ K ++ (T ++ P ++ R)) (P ++ F ++ Pc ++ K ++ (T ++ R)).
Proof.
intros. eapply Permutation_trans; [|eapply Permutation_trans; [apply (Permutation_app_swap_app (F ++ Pc ++ K ++ T) P R)|]];
rewrite <- ?app_assoc; apply Permutation_refl.
Qed.
Lemma groups_drop_cf : forall (P rest F : list batch) (GS : list (list batch)),
P ++ rest = F ++ concat GS -> Forall bfull (removelast F) -> Forall qgroup_ok GS ->
exists F' GS', rest = F' ++ concat GS' /\ Forall bfull (removelast F') /\ Forall qgroup_ok GS'.
Proof.
induction P as [|b P IH]; intros rest F GS E FF FG.
- exists F, GS. cbn [app] in E. auto.
- destruct F as [|b' F0].
+ destruct GS as [|g GS0]; [cbn in E; discriminate|]. inversion FG as [|g' GS' (GN & GF & _) FG0]; subst.
destruct g as [|b0 g0]; [exfalso; apply GN; reflexivity|]. cbn [app concat] in E. injection E as _ E.
apply (IH rest g0 GS0 E); [exact (Forall_removelast_tl_cf _ _ _ GF) | exact FG0].
+ cbn [app] in E. injection E as _ E. apply (IH rest F0 GS E); [exact (Forall_removelast_tl_cf _ _ _ FF) | exact FG].
Qed.
Lemma RI_pop_cf : forall U pp cc bb s P rest,
WfR_cf U pp cc bb s -> qc_list (st_qglobal s) = P ++ rest ->
RI_cf U pp cc bb (set_qglobal (mkQC rest (qc_bytes (st_qglobal s) - sum_bytes P)) s) P.
Proof.
intros U pp cc bb s P rest W EP. wfr_fields_y3 W. quar_fields Xq.
set (s' := set_qglobal _ s).
assert (AB : all_batches s = qc_list (st_qthread s) ++ P ++ rest) by (unfold all_batches; rewrite EP; reflexivity).
assert (AB' : all_batches s' = qc_list (st_qthread s) ++ rest) by reflexivity.
assert (PB : Permutation (P ++ all_batches s') (all_batches s)). { rewrite AB, AB'. apply Permutation_app_swap_app. }
assert (PQ : Permutation (flat_map b_items P ++ q_items s') (q_items s)).
{ unfold q_items. rewrite <- flat_map_app. apply Permutation_flat_map. exact PB. }
pose proof (Xcl kBatchClass ltac:(unfold kBatchClass; lia)) as C24. unfold wf_class_cf in C24.
assert (PE : Permutation (fa_elems (class_size kBatchClass) (rg_free (reg s kBatchClass)) ++ pc_chunks (cache s kBatchClass) ++ chunk_offs s kBatchClass ++ batch_offs s kBatchClass)
(map (fun b => b_self b - region_off kBatchClass) P ++ class_elems s' kBatchClass)).
{ unfold class_elems. subst s'. cbn [set_qglobal]. change (reg (set_qglobal ?g s) ?c) with (reg s c). change (cache (set_qglobal ?g s) ?c) with (cache s c).
rewrite (chunk_offs_begs_cf s (set_qglobal _ s)) by reflexivity. rewrite !batch_offs_24_cf, AB', AB, !map_app. apply perm_insert4_cf. }
split; [|split; [|split; [|split; [|split]]]].
- constructor; wfr_easy_y3.
+ intros c Hc. unfold wf_class_cf. subst s'. cbn [st_cache_inited set_qglobal].
change (reg (set_qglobal ?g s) c) with (reg s c). change (cache (set_qglobal ?g s) c) with (cache s c).
rewrite (chunk_offs_begs_cf s) by reflexivity. pose proof (Xcl c Hc) as C. unfold wf_class_cf in C.
destruct (Z.eq_dec c kBatchClass) as [->|Hne].
* eapply (cls_ok_repart_cf _ _ _ _ _ _ _ _ _ _ _ (map (fun b => b_self b - region_off kBatchClass) P)); try reflexivity;
[exact C | exact (wrc_runs _ _ _ _ _ _ C) | exact (wrc_fa_len _ _ _ _ _ _ C) | exact (wrc_cache _ _ _ _ _ _ C) |].
unfold class_elems in PE. exact PE.
* rewrite !batch_offs_other_cf in * by exact Hne. exact C.
+ constructor; subst s'; cbn [st_qthread st_qglobal st_chunks set_qglobal qc_bytes qc_list]; try assumption.
* rewrite Qbg, EP, sum_bytes_app_cf. lia.
* eapply (proj1 (Forall_app _ P _)). eapply Forall_Permutation; [apply Permutation_sym; exact PB | exact Qbat].
* eapply (proj1 (Forall_app _ (flat_map b_items P) _)). eapply Forall_Permutation; [apply Permutation_sym; exact PQ | exact Qit].
* pose proof (NoDup_Permutation _ _ (Permutation_map ck_beg (Permutation_sym PQ)) Qnd) as ND. rewrite map_app in ND.
apply NoDup_app_iff in ND as (_ & ND & _). exact ND.
* destruct Qgr as (F & GS & EG & FF & FG). rewrite EP in EG. exact (groups_drop_cf P rest F GS EG FF FG).
+ subst s'. cbn [st_nev set_qglobal]. pose proof (Permutation_length PB) as L. rewrite length_app in L. lia.
+ subst s'. cbn [st_cache_inited set_qglobal]. intros NE. apply Xqi. rewrite AB, AB' in *. intros E. apply NE.
apply app_eq_nil in E as [E1 E2]. apply app_eq_nil in E2 as [_ E3]. rewrite E1, E3. reflexivity.
+ (* wfr_qsize: the pop drops the popped batches' items *)
pose proof (Forall_Permutation _ _ _ (Permutation_sym PQ) Xqs) as FQ. apply Forall_app in FQ as [_ FQ]. exact FQ.
- apply Forall_forall. intros k Hk.
pose proof (proj1 (Forall_forall _ _) Qit k ltac:(eapply Permutation_in; [exact PQ | apply in_app_iff; left; exact Hk])) as [H1 H2]. subst s'. cbn. auto.
- eapply NoDup_Permutation; [apply Permutation_map; apply Permutation_sym; exact PQ | exact Qnd].
- pose proof (Forall_Permutation _ _ _ (Permutation_sym PB) Qbat) as FB. apply Forall_app in FB as [FB _].
eapply Forall_impl; [|exact FB]. cbv beta. intros b Hb. lia.
- pose proof (Forall_Permutation _ _ _ PE (wrc_elems _ _ _ _ _ _ C24)) as FE. apply Forall_app in FE as [FE _].
pose proof (Permutation_NoDup PE (wrc_nodup _ _ _ _ _ _ C24)) as ND. apply NoDup_app_iff in ND as (ND1 & _ & ND3).
apply Forall_forall. intros b Hb.
pose proof (proj1 (Forall_forall _ _) FE _ (in_map (fun b => b_self b - region_off kBatchClass) _ _ Hb)) as [E1 E2].
change (reg s' kBatchClass) with (reg s kBatchClass). split; [exact E1 | split; [exact E2|]].
intros Hin. exact (ND3 _ (in_map (fun b => b_self b - region_off kBatchClass) _ _ Hb) Hin).
- pose proof (Permutation_NoDup PE (wrc_nodup _ _ _ _ _ _ C24)) as ND. apply NoDup_app_iff in ND as (ND1 & _).
rewrite boffs_map_cf in ND1. apply NoDup_map_inv in ND1. exact ND1.
Qed.
Lemma reg_upd_pc_cf : forall c p s c', reg (upd_pc c p s) c' = reg s c'. Proof. reflexivity. Qed.
Lemma chunk_offs_upd_pc_cf : forall c p s c', chunk_offs (upd_pc c p s) c' = chunk_offs s c'. Proof. reflexivity. Qed.
Lemma batch_offs_upd_pc_cf : forall c p s c', batch_offs (upd_pc c p s) c' = batch_offs s c'. Proof. reflexivity. Qed.
Lemma chunk_offs_upd_reg_cf : forall c r s c', chunk_offs (upd_reg c r s) c' = chunk_offs s c'. Proof. reflexivity. Qed.
Lemma batch_offs_upd_reg_cf : forall c r s c', batch_offs (upd_reg c r s) c' = batch_offs s c'. Proof. reflexivity. Qed.
Lemma cache_upd_reg_cf : forall c r s c', cache (upd_reg c r s) c' = cache s c'. Proof. reflexivity. Qed.
Lemma cache_upd_pc_other_cf : forall c c' p s, 0 <= c -> 0 <= c' -> c <> c' -> cache (upd_pc c p s) c' = cache s c'.
Proof. intros c c' p s H1 H2 H3. unfold upd_pc, cache. cbn [st_cache set_cache]. apply znth_zupd_other; lia. Qed.
Lemma class_elems_upd_pc_same_cf : forall c p s, 0 <= c -> (Z.to_nat c < length (st_cache s))%nat ->
class_elems (upd_pc c p s) c = fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks p ++ chunk_offs s c ++ batch_offs s c.
Proof. intros c p s Hc Hl. unfold class_elems. rewrite cache_upd_pc by (exact Hc || exact Hl). reflexivity. Qed.
Lemma class_elems_upd_pc_other_cf : forall c c' p s, 0 <= c -> 0 <= c' -> c <> c' -> class_elems (upd_pc c p s) c' = class_elems s c'.
Proof. intros c c' p s H1 H2 H3. unfold class_elems. rewrite cache_upd_pc_other_cf by assumption. reflexivity. Qed.
Lemma class_elems_upd_reg_other_cf : forall c c' r s, 0 <= c -> 0 <= c' -> c <> c' -> class_elems (upd_reg c r s) c' = class_elems s c'.
Proof. intros c c' r s H1 H2 H3. unfold class_elems. rewrite reg_upd_reg_other by assumption. reflexivity. Qed.
Lemma class_elems_count_cf : forall U pp cc bb s c, WfR_cf U pp cc bb s -> 1 <= c <= 31 ->
32 * (fa_len (rg_free (reg s c)) + Z.of_nat (length (pc_chunks (cache s c)))) <= rg_alloc_user (reg s c) /\
rg_alloc_user (reg s c) <= kFreeArrayOffset.
Proof.
intros U pp cc bb s c W Hc. pose proof (class_ok c Hc) as (Ksz & K32 & _).
pose proof (wfr_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_nodup _ _ _ _ _ _ C) as ND. pose proof (wrc_elems _ _ _ _ _ _ C) as EL. pose proof (wrc_runs _ _ _ _ _ _ C) as R.
pose proof (wrc_alloc _ _ _ _ _ _ C) as A. pose proof (wrc_alloc_al _ _ _ _ _ _ C) as AL.
rewrite app_assoc in ND, EL. apply NoDup_app_iff in ND as (ND & _ & _). apply Forall_app in EL as [EL _].
pose proof (multiples_bound (class_size c) (rg_alloc_user (reg s c)) _ Ksz ltac:(lia) AL ND EL) as MB.
rewrite length_app, Nat2Z.inj_add in MB. rewrite <- (fa_elems_length (class_size c)) by exact R.
pose proof (mapped_bound_r_cf U pp cc bb s c W Hc). pose proof (wfr_slack _ _ _ _ _ W).
assert (K32' : 32 <= class_size c). { apply Z.mod_divide in K32 as [k Hk]; [nia | lia]. }
pose proof (fa_len_nonneg _ R). unfold kFreeArrayOffset in *. nia.
Qed.
Lemma cls_ok_add_pc_cf : forall c r p ko bo x,
cls_ok_cf c r p true ko bo ->
~ In x (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) ->
0 <= x < rg_alloc_user r -> x mod class_size c = 0 ->
Z.of_nat (length (pc_chunks p)) + 1 <= max_cached c ->
cls_ok_cf c r (mkPC (pc_max p) (pc_chunks p ++ [x])) true ko bo.
Proof.
intros c r p ko bo x C Hni Hx Hm Hlen.
pose proof (cls_ok_add_ko_cf c r p true ko bo x C Hni Hx Hm) as C'.
eapply (cls_ok_repart_cf c r p true (ko ++ [x]) bo r _ true ko bo []); try reflexivity;
[exact C' | exact (wrc_runs _ _ _ _ _ _ C) | exact (wrc_fa_len _ _ _ _ _ _ C) | |].
- cbn [pc_max pc_chunks]. pose proof (wrc_cache _ _ _ _ _ _ C) as [PM PL]. rewrite length_app. cbn [length]. split; [exact PM | lia].
- cbn [app pc_chunks]. apply Permutation_app_head. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply Permutation_sym. apply Permutation_middle.
Qed.
Definition cache_dealloc_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (c x : Z) (ns : bool) (res : unit * astate) : Prop :=
let s' := snd res in
WfR_cf U pp cc bb s' /\ regs_only s s' /\ st_cache_inited s' = true /\
(forall c', 0 <= c' <= 31 -> rg_alloc_user (reg s' c') = rg_alloc_user (reg s c')) /\
(forall c' y, 0 <= c' <= 31 -> In y (class_elems s' c') -> (y = x /\ c' = c) \/ In y (class_elems s c')) /\
(forall c', 0 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s' c')) /\
(forall c', 0 <= c' <= 31 -> length (class_elems s' c') = (length (class_elems s c') + (if (c' =? c)%Z then 1 else 0))%nat).
Lemma cache_dealloc_ok_cf : forall U pp cc bb s c off ns,
WfR_cf U pp cc bb s -> 1 <= c <= 31 ->
0 <= off - region_off c < rg_alloc_user (reg s c) -> (off - region_off c) mod class_size c = 0 ->
~ In (off - region_off c) (class_elems s c) ->
atok ns (cache_dealloc c off s) (cache_dealloc_post_cf U pp cc bb s c (off - region_off c)).
Proof.
intros U pp cc bb s c off ns W Hc Hx Hxm Hxni. set (x := off - region_off c) in *.
pose proof (class_ok c Hc) as (Ksz & K32 & Kmax & Kmc & Kmc2 & Kmcs).
unfold cache_dealloc. apply atok_bind. unfold init_cache_if_needed. apply atok_bind. apply atok_get. cbn [fst snd].
assert (STEP1 : forall s1, WfR_cf U pp cc bb s1 -> st_cache_inited s1 = true -> regs_only s s1 -> st_regions s1 = st_regions s ->
(forall c', 0 <= c' <= 31 -> pc_chunks (cache s1 c') = pc_chunks (cache s c')) ->
atok ns ((p <- get_pc c ;;
(if Z.of_nat (length (pc_chunks p)) =? pc_max p
then return_to_allocator c (skipn (length (pc_chunks p) - Z.to_nat (pc_max p / 2)) (pc_chunks p)) ;;
set_pc c (mkPC (pc_max p) (firstn (length (pc_chunks p) - Z.to_nat (pc_max p / 2)) (pc_chunks p)))
else ret tt) ;;
p <- get_pc c ;; set_pc c (mkPC (pc_max p) (pc_chunks p ++ [x]))) s1)
(cache_dealloc_post_cf U pp cc bb s c x)).
2:{ destruct (st_cache_inited s) eqn:Ei.
- apply atok_ret. apply (STEP1 s W Ei (regs_only_refl s) eq_refl). intros; reflexivity.
- apply atok_put. apply STEP1; [apply WfR_init_caches_cf; [exact W | exact Ei] | reflexivity | unfold regs_only; cbn; repeat split; reflexivity | reflexivity |].
intros c' Hc'. cbn [snd]. rewrite cache_after_init by exact Hc'. reflexivity. }
intros s1 W1 Hi1 RO1 ER1 EC1.
assert (HL : (Z.to_nat c < length (st_regions s1))%nat) by (eapply WfR_len_regions_cf; [exact W1 | lia]).
assert (HLc : (Z.to_nat c < length (st_cache s1))%nat) by (eapply WfR_len_cache_cf; [exact W1 | lia]).
assert (EREG : forall c', reg s1 c' = reg s c') by (intros c'; unfold reg; rewrite ER1; reflexivity).
assert (ECE : forall c', 0 <= c' <= 31 -> class_elems s1 c' = class_elems s c').
{ intros c' Hc'. unfold class_elems. rewrite EREG, EC1 by exact Hc'. destruct RO1 as (Rck & _ & _ & _ & Rqt & Rqg & _).
rewrite (chunk_offs_begs_cf s s1) by (rewrite Rck; reflexivity). unfold batch_offs, all_batches. rewrite Rqt, Rqg. reflexivity. }
pose proof (wfr_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class_cf in C1. rewrite Hi1 in C1. pose proof (wrc_cache _ _ _ _ _ _ C1) as [PM1 PL1].
assert (PUSH : forall ns4 s4 p4, WfR_cf U pp cc bb s4 -> st_cache_inited s4 = true -> regs_only s s4 ->
(forall c', 0 <= c' <= 31 -> rg_alloc_user (reg s4 c') = rg_alloc_user (reg s c')) ->
cache s4 c = p4 -> Permutation (class_elems s4 c) (class_elems s c) ->
(forall c', 0 <= c' <= 31 -> c' <> c -> class_elems s4 c' = class_elems s c') ->
pc_max p4 = max_cached c -> Z.of_nat (length (pc_chunks p4)) + 1 <= max_cached c ->
(Z.to_nat c < length (st_cache s4))%nat ->
(forall c', 0 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s4 c')) ->
atok ns4 ((p <- get_pc c ;; set_pc c (mkPC (pc_max p) (pc_chunks p ++ [x]))) s4) (cache_dealloc_post_cf U pp cc bb s c x)).
{ intros ns4 s4 p4 W4 Hi4 RO4 AU4 EC4 P4 OC4 PM4 PL4 HLc4 MFA4. pose proof (MFA4 c ltac:(lia)) as MF4.
apply atok_bind. apply atok_get_pc. cbn [fst snd]. rewrite EC4. apply atok_set_pc.
pose proof (wfr_classes _ _ _ _ _ W4 c Hc) as C4. unfold wf_class_cf in C4. rewrite EC4, Hi4 in C4.
split; [|split; [|split; [|split; [|split; [|split]]]]].
- eapply WfR_set_pc_y3; [exact W4 | exact Hc |].
{ rewrite Hi4. apply cls_ok_add_pc_cf; [exact C4 | | | exact Hxm | exact PL4].
+ intros Hin. apply Hxni. eapply Permutation_in; [exact P4|]. unfold class_elems. rewrite EC4. exact Hin.
+ rewrite AU4 by lia. exact Hx. }
- destruct RO4 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold regs_only, upd_pc. cbn. repeat split; assumption.
- cbn [snd st_cache_inited upd_pc set_cache]. exact Hi4.
- intros c' Hc'. cbn [snd]. rewrite reg_upd_pc_cf. apply AU4. exact Hc'.
- intros c' y Hc' Hin. cbn [snd] in Hin.
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite class_elems_upd_pc_same_cf in Hin by (lia || exact HLc4). cbn [pc_chunks] in Hin.
assert (Hin' : In y (class_elems s4 c ++ [x])).
{ unfold class_elems. rewrite EC4. rewrite !in_app_iff in Hin |- *. cbn [In] in *. tauto. }
apply in_app_iff in Hin' as [Hin'|[<-|[]]]; [right; eapply Permutation_in; [exact P4 | exact Hin'] | left; split; reflexivity].
+ right. rewrite class_elems_upd_pc_other_cf in Hin by lia. rewrite <- (OC4 c') by lia. exact Hin.
- intros c' Hc'. cbn [snd]. rewrite reg_upd_pc_cf. apply MFA4. exact Hc'.
- intros c' Hc'. cbn [snd]. destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite class_elems_upd_pc_same_cf by (lia || exact HLc4). cbn [pc_chunks]. rewrite Z.eqb_refl.
pose proof (Permutation_length P4) as L4. unfold class_elems in L4 |- *. rewrite EC4 in L4.
rewrite !length_app in L4. rewrite !length_app. cbn [length] in L4 |- *. lia.
+ rewrite class_elems_upd_pc_other_cf by lia. rewrite (OC4 c') by lia. destruct (Z.eqb_spec c' c); [lia | lia]. }
apply atok_bind. apply atok_get_pc. cbn [fst snd]. rewrite PM1.
destruct (Z.eqb_spec (Z.of_nat (length (pc_chunks (cache s1 c)))) (max_cached c)) as [FULL|NF].
-
set (l := pc_chunks (cache s1 c)) in *. set (n := max_cached c / 2).
assert (N1 : 1 <= n <= 8) by (subst n; split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
assert (N3 : n + 1 <= max_cached c) by (subst n; pose proof (Z.mul_div_le (max_cached c) 2 ltac:(lia)); lia).
set (keep := firstn (length l - Z.to_nat n) l). set (drained := skipn (length l - Z.to_nat n) l).
assert (EL : l = keep ++ drained) by (subst keep drained; symmetry; apply firstn_skipn).
assert (LD : Z.of_nat (length drained) = n) by (subst drained; rewrite length_skipn; lia).
assert (LK : Z.of_nat (length keep) = max_cached c - n) by (subst keep; rewrite length_firstn; lia).
apply atok_bind. unfold return_to_allocator. apply atok_bind. apply atok_bind. apply atok_get_region. cbn [fst snd].
pose proof (class_elems_count_cf U pp cc bb s1 c W1 Hc) as [CNT A31].
pose proof (wrc_fa_len _ _ _ _ _ _ C1) as FL. pose proof (fa_len_nonneg _ (wrc_runs _ _ _ _ _ _ C1)) as FL0.
apply atok_bind.
eapply atok_mono; [|apply (ensure_free_array_ok_y3 U pp cc bb s1 c (fa_len (rg_free (reg s1 c)) + Z.of_nat (length drained)) true ns W1 Hc)].
2:{ lia. } 2:{ unfold kFreeArrayMapSize. lia. } 2:{ unfold kFreeArrayMax, kFreeArrayOffset in *. fold l in CNT. lia. }
intros ns2 [ok s2] (r2 & -> & W2 & M2 & A2 & F2 & FA2 & OK2 & NS2). cbn [fst snd].
destruct ok; [|destruct (NS2 eq_refl); discriminate]. specialize (OK2 eq_refl). clear NS2.
apply atok_bind. apply atok_get_region. rewrite reg_upd_reg by (lia || exact HL). cbn [fst snd].
apply atok_set_region. cbn [fst snd]. rewrite upd_reg_upd_reg. apply atok_set_pc.
set (R := mkRegion _ _ _ _ _).
pose proof (fa_push_list_spec (class_size c) (rg_free r2) drained) as (PE1 & PE2 & PE3).
pose proof (wfr_classes _ _ _ _ _ W2 c Hc) as C2. unfold wf_class_cf in C2.
rewrite reg_upd_reg, cache_upd_reg_cf, chunk_offs_upd_reg_cf, batch_offs_upd_reg_cf in C2 by (lia || exact HL).
replace (st_cache_inited (upd_reg c r2 s1)) with true in C2 by (symmetry; exact Hi1).
assert (PERM : forall K B : list Z, Permutation (fa_elems (class_size c) (rg_free r2) ++ (keep ++ drained) ++ K ++ B)
((rev drained ++ fa_elems (class_size c) (rg_free r2)) ++ keep ++ K ++ B)).
{ intros K B. rewrite <- !app_assoc. rewrite (app_assoc (fa_elems (class_size c) (rg_free r2)) keep (drained ++ K ++ B)).
eapply Permutation_trans; [apply Permutation_app_swap_app|].
rewrite <- !app_assoc. apply Permutation_app; [apply Permutation_rev | apply Permutation_refl]. }
assert (W4 : WfR_cf U pp cc bb (upd_pc c (mkPC (max_cached c) keep) (upd_reg c R s1))).
{ rewrite <- (upd_reg_upd_reg c r2 R s1). eapply (WfR_set_region_pc_y3 U pp cc bb (upd_reg c r2 s1) c R _ pp W2 Hc).
- replace (st_cache_inited (upd_reg c r2 s1)) with true by (symmetry; exact Hi1). rewrite chunk_offs_upd_reg_cf, batch_offs_upd_reg_cf.
eapply (cls_ok_repart_cf c r2 (cache s1 c) true _ _ R _ true _ _ []); try exact C2; try reflexivity.
+ apply PE3. exact (wrc_runs _ _ _ _ _ _ C2).
+ subst R. cbnr. rewrite PE2, F2. lia.
+ cbn [pc_max pc_chunks]. split; [reflexivity | lia].
+ cbn [app pc_chunks]. subst R. cbnr. rewrite PE1. fold l. rewrite EL. apply PERM.
- pose proof (wfr_slack _ _ _ _ _ W2). lia.
- rewrite reg_upd_reg by (lia || exact HL). subst R. cbnr. pose proof (wfr_prim_ev _ _ _ _ _ W2). lia. }
assert (HLc4 : (Z.to_nat c < length (st_cache (upd_pc c (mkPC (max_cached c) keep) (upd_reg c R s1))))%nat).
{ unfold upd_pc, upd_reg. cbn [st_cache set_cache set_regions]. rewrite zupd_length. exact HLc. }
apply (PUSH ns2 _ (mkPC (max_cached c) keep) W4); try reflexivity.
+ cbn [st_cache_inited upd_pc upd_reg set_cache set_regions]. exact Hi1.
+ destruct RO1 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold regs_only, upd_pc, upd_reg. cbn. repeat split; assumption.
+ intros c' Hc'. rewrite reg_upd_pc_cf. destruct (Z.eq_dec c c') as [<-|Hne].
* rewrite reg_upd_reg by (lia || exact HL). subst R. cbnr. rewrite A2, EREG. reflexivity.
* rewrite reg_upd_reg_other by lia. rewrite EREG. reflexivity.
+ apply cache_upd_pc; [lia | unfold upd_reg; cbn [st_cache set_regions]; exact HLc].
+ rewrite <- (ECE c) by lia. rewrite class_elems_upd_pc_same_cf by (lia || unfold upd_reg; cbn [st_cache set_regions]; exact HLc).
rewrite reg_upd_reg, chunk_offs_upd_reg_cf, batch_offs_upd_reg_cf by (lia || exact HL). cbn [pc_chunks]. subst R. cbnr. rewrite PE1.
unfold class_elems. fold l. rewrite EL, <- F2. apply Permutation_sym. apply PERM.
+ intros c' Hc' Hne. rewrite class_elems_upd_pc_other_cf, class_elems_upd_reg_other_cf by lia. apply ECE. exact Hc'.
+ cbn [pc_chunks]. lia.
+ exact HLc4.
+ intros c' Hc'. rewrite reg_upd_pc_cf. destruct (Z.eq_dec c c') as [<-|Hne].
* rewrite reg_upd_reg by (lia || exact HL). subst R. cbnr. rewrite <- EREG. exact FA2.
* rewrite reg_upd_reg_other by lia. rewrite EREG. apply Z.le_refl.
-
apply atok_bind. apply atok_ret. cbn [fst snd].
apply (PUSH ns s1 (cache s1 c) W1 Hi1 RO1); try reflexivity.
+ intros c' Hc'. rewrite EREG. reflexivity.
+ rewrite ECE by lia. apply Permutation_refl.
+ intros c' Hc' _. apply ECE. exact Hc'.
+ exact PM1.
+ lia.
+ exact HLc.
+ intros c' Hc'. rewrite EREG. apply Z.le_refl.
Qed.
Lemma chunk_offs_list_app_cf : forall s l1 l2 c, chunk_offs (set_chunks (l1 ++ l2) s) c = chunk_offs (set_chunks l1 s) c ++ chunk_offs (set_chunks l2 s) c.
Proof. intros s l1 l2 c. unfold chunk_offs. cbn [st_chunks set_chunks]. rewrite flat_map_app. reflexivity. Qed.
Lemma chunk_offs_one_cf : forall s k c, chunk_offs (set_chunks [k] s) c =
match ck_beg k with PPrim off => if prim_class off =? c then [off - region_off c] else [] | _ => [] end.
Proof. intros s k c. unfold chunk_offs. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma class_elems_del_cf : forall s l1 k l2 c,
st_chunks s = l1 ++ k :: l2 ->
Permutation (class_elems s c) (chunk_offs (set_chunks [k] s) c ++ class_elems (set_chunks (l1 ++ l2) s) c).
Proof.
intros s l1 k l2 c E. unfold class_elems. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks.
replace (chunk_offs s c) with (chunk_offs (set_chunks (l1 ++ k :: l2) s) c) by (rewrite <- E; destruct s; reflexivity).
change (k :: l2) with ([k] ++ l2). rewrite !chunk_offs_list_app_cf.
set (F := fa_elems _ _). set (P := pc_chunks _). set (A := chunk_offs (set_chunks l1 s) c). set (X := chunk_offs (set_chunks [k] s) c).
set (B := chunk_offs (set_chunks l2 s) c). set (Q := batch_offs s c).
eapply Permutation_trans; [|eapply Permutation_trans; [apply (Permutation_app_swap_app (F ++ P ++ A) X (B ++ Q))|]];
rewrite <- ?app_assoc; apply Permutation_refl.
Qed.
Lemma WfR_del_prim_cf : forall U pp cc bb s l1 k l2 off,
WfR_cf U pp cc bb s -> st_chunks s = l1 ++ k :: l2 -> ck_beg k = PPrim off -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items s)) ->
WfR_cf U pp cc bb (set_chunks (l1 ++ l2) s) /\
let c := prim_class off in let x := off - region_off c in
1 <= c <= 30 /\ 0 <= x < rg_alloc_user (reg s c) /\ x mod class_size c = 0 /\ ~ In x (class_elems (set_chunks (l1 ++ l2) s) c) /\
(forall c' y, In y (class_elems (set_chunks (l1 ++ l2) s) c') -> In y (class_elems s c')).
Proof.
intros U pp cc bb s l1 k l2 off W E Hb Hst Hni.
assert (Hk : In k (st_chunks s)) by (rewrite E; apply in_elt).
pose proof (prim_chunk_off_y3 U pp cc bb s k off W Hk Hb) as (G1 & G2 & G3 & G4 & G5 & G6). cbv zeta in *.
set (c := prim_class off) in *. set (x := off - region_off c) in *.
assert (X1 : chunk_offs (set_chunks [k] s) c = [x]) by (rewrite chunk_offs_one_cf, Hb; fold c; rewrite Z.eqb_refl; reflexivity).
assert (X0 : forall c', c' <> c -> chunk_offs (set_chunks [k] s) c' = []).
{ intros c' Hc'. rewrite chunk_offs_one_cf, Hb. fold c. destruct (Z.eqb_spec c c'); [lia | reflexivity]. }
wfr_fields_y3 W. quar_fields Xq.
assert (ND : NoDup (map ck_beg (l1 ++ k :: l2))) by (rewrite <- E; exact Xnd).
pose proof (Xcl c ltac:(lia)) as C. unfold wf_class_cf in C.
pose proof (class_elems_del_cf s l1 k l2 c E) as PE. rewrite X1 in PE. cbn [app] in PE.
pose proof (wrc_elems _ _ _ _ _ _ C) as EL. pose proof (wrc_alloc _ _ _ _ _ _ C) as AL.
assert (INX : In x (class_elems s c)) by (eapply Permutation_in; [apply Permutation_sym; exact PE | left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) EL x INX) as [Ex1 Ex2].
split; [|split; [lia | split; [lia | split; [exact Ex2 | split]]]].
- constructor; wfr_easy_y3.
+ intros c' Hc'. unfold wf_class_cf. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks. cbn [st_cache_inited set_chunks].
pose proof (Xcl c' Hc') as C'. unfold wf_class_cf in C'.
pose proof (class_elems_del_cf s l1 k l2 c' E) as PE'. unfold class_elems in PE'. rewrite reg_set_chunks, cache_set_chunks, batch_offs_set_chunks in PE'.
eapply (cls_ok_repart_cf c' _ _ _ _ _ _ _ _ _ _ (chunk_offs (set_chunks [k] s) c')); try reflexivity;
[exact C' | exact (wrc_runs _ _ _ _ _ _ C') | exact (wrc_fa_len _ _ _ _ _ _ C') | exact (wrc_cache _ _ _ _ _ _ C') | exact PE'].
+ cbn [st_chunks set_chunks]. rewrite E in Xck. apply Forall_app in Xck as [X1' X2']. inversion X2'; subst.
apply Forall_app. split; [eapply Forall_chunk_ok_cf_ext; [reflexivity | exact X1'] | eapply Forall_chunk_ok_cf_ext; [reflexivity | eassumption]].
+ cbn [st_chunks set_chunks]. rewrite map_app in ND |- *. cbn [map] in ND. exact (NoDup_remove_1 _ _ _ ND).
+ cbn [st_chunks set_chunks st_nev]. rewrite E, !length_app in Xcev. rewrite length_app. cbn [length] in Xcev. lia.
+ rewrite blocks_bytes_eq_cf in *. cbn [st_chunks set_chunks]. rewrite E, bbytes_split_cf in Xlive. unfold is_alloc in Xlive. rewrite Hst in Xlive. lia.
+ constructor; cbn [st_qthread st_qglobal st_chunks set_chunks]; rewrite ?all_batches_set_chunks, ?q_items_set_chunks; try assumption.
apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) Qit k' Hk') as [H1 H2]. split; [|exact H2].
rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply in_app_iff; left; exact H1 | exfalso | apply in_app_iff; right; exact H1].
apply Hni. apply in_map. exact Hk'.
+ sec_fields_cf Xsec. constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_chunks]; try assumption.
intros r. rewrite Sac, E. split; intros (k' & Hk' & Hb'); apply in_app_iff in Hk' as [Hk'|Hk'].
* exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb'].
* destruct Hk' as [<-|Hk']; [congruence|]. exists k'. split; [apply in_app_iff; right; exact Hk' | exact Hb'].
* exists k'. split; [apply in_app_iff; left; exact Hk' | exact Hb'].
* exists k'. split; [apply in_app_iff; right; right; exact Hk' | exact Hb'].
- pose proof (Permutation_NoDup PE (wrc_nodup _ _ _ _ _ _ C)) as NDx. inversion NDx; subst. assumption.
- intros c' y Hy. destruct (Z.eq_dec c' c) as [->|Hne].
+ eapply Permutation_in; [apply Permutation_sym; exact PE | right; exact Hy].
+ pose proof (class_elems_del_cf s l1 k l2 c' E) as PE'. rewrite (X0 c' Hne) in PE'. cbn [app] in PE'.
eapply Permutation_in; [apply Permutation_sym; exact PE' | exact Hy].
Qed.
Lemma index_of_spec_cf : forall l r i0, In r l -> exists j, index_of l r i0 = Some (i0 + j)%nat /\ nth_error l j = Some r.
Proof.
induction l as [|y t IH]; intros r i0 Hin; [destruct Hin|]. cbn [index_of].
destruct (Nat.eqb_spec y r) as [->|Hne].
- exists 0%nat. rewrite Nat.add_0_r. split; reflexivity.
- destruct Hin as [->|Hin]; [congruence|]. destruct (IH r (S i0) Hin) as (j & E1 & E2).
exists (S j). rewrite E1. split; [f_equal; lia | exact E2].
Qed.
Lemma lupd_app_mid_cf : forall {X} (a1 : list X) y a2 v, lupd (a1 ++ y :: a2) (length a1) v = a1 ++ v :: a2.
Proof. intros X a1. induction a1 as [|h t IH]; intros y a2 v; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.
Lemma removelast_last2_cf : forall {X} (l : list X) a, removelast (l ++ [a]) = l.
Proof.
intros X l a. induction l as [|h t IH]; [reflexivity|]. cbn [app removelast]. rewrite IH.
destruct t as [|h' t']; cbn; reflexivity.
Qed.
Lemma swap_remove_perm_cf : forall (arr : list nat) i r,
nth_error arr i = Some r -> Permutation (r :: removelast (lupd arr i (last arr r))) arr.
Proof.
intros arr i r Hn.
destruct (nth_error_split arr i Hn) as (a1 & a2 & -> & <-).
destruct (list_eq_dec Nat.eq_dec a2 []) as [->|Hne].
- replace (last (a1 ++ [r]) r) with r by (rewrite last_last; reflexivity). rewrite lupd_app_mid_cf, removelast_last2_cf. apply Permutation_cons_append.
- pose proof (app_removelast_last r Hne) as E. set (z := last a2 r) in *. set (a2' := List.removelast a2) in *.
rewrite E. replace (last (a1 ++ r :: a2' ++ [z]) r) with z.
2:{ rewrite app_comm_cons, app_assoc, last_last. reflexivity. }
rewrite lupd_app_mid_cf. replace (a1 ++ z :: a2' ++ [z]) with ((a1 ++ z :: a2') ++ [z]) by (rewrite <- app_assoc; reflexivity).
rewrite removelast_last2_cf. apply Permutation_cons_app. apply Permutation_app_head. apply Permutation_cons_append.
Qed.
Lemma chunk_offs_del_sec_cf : forall s l1 k l2 r o c, st_chunks s = l1 ++ k :: l2 -> ck_beg k = PSec r o ->
chunk_offs (set_chunks (l1 ++ l2) s) c = chunk_offs s c.
Proof.
intros s l1 k l2 r o c E Hb.
replace (chunk_offs s c) with (chunk_offs (set_chunks (l1 ++ k :: l2) s) c) by (rewrite <- E; destruct s; reflexivity).
change (k :: l2) with ([k] ++ l2). rewrite !chunk_offs_list_app_cf, chunk_offs_one_cf, Hb. reflexivity.
Qed.
Lemma Forall_lupd_cf : forall {X} (P : X -> Prop) (l : list X) i v, Forall P l -> P v -> Forall P (lupd l i v).
Proof.
intros X P l. induction l as [|h t IH]; intros i v HF Hv; [destruct i; exact HF|].
inversion HF as [|? ? Hh Ht]; subst. destruct i as [|i]; cbn [lupd]; constructor; auto.
Qed.
Lemma WfR_del_sec_cf : forall U pp cc bb s l1 k l2 r sm i,
WfR_cf U pp cc bb s -> st_chunks s = l1 ++ k :: l2 -> ck_beg k = PSec r kPage -> ck_state k = CQuarantined ->
~ In (ck_beg k) (map ck_beg (q_items s)) ->
nth_error (st_secs s) r = Some sm -> nth_error (st_sec_arr s) i = Some r ->
WfR_cf U pp cc bb (set_sec_arr (removelast (lupd (st_sec_arr s) i (last (st_sec_arr s) r)))
(set_secs (lupd (st_secs s) r (mkSec (sm_len sm) (sm_size sm) false)) (set_chunks (l1 ++ l2) s))).
Proof.
intros U pp cc bb s l1 k l2 r sm i W E Hb Hst Hni Hsm Hi.
assert (Hk : In k (st_chunks s)) by (rewrite E; apply in_elt).
wfr_fields_y3 W. quar_fields Xq. sec_fields_cf Xsec.
assert (ND : NoDup (map ck_beg (l1 ++ k :: l2))) by (rewrite <- E; exact Xnd).
rewrite map_app in ND. cbn [map] in ND. pose proof (NoDup_remove_1 _ _ _ ND) as ND'. apply NoDup_app_iff in ND as (NDa & NDb & NDc). inversion NDb; subst.
pose proof (swap_remove_perm_cf _ _ _ Hi) as PA. set (arr' := removelast (lupd _ _ _)) in *.
assert (NDA : NoDup arr' /\ ~ In r arr').
{ pose proof (NoDup_Permutation _ _ (Permutation_sym PA) Snd) as X. inversion X; subst. auto. }
destruct NDA as [NDA NIA].
assert (INA : forall r', In r' arr' <-> In r' (st_sec_arr s) /\ r' <> r).
{ intros r'. split.
- intros H. split; [eapply Permutation_in; [exact PA | right; exact H] | intros ->; exact (NIA H)].
- intros [H Hne]. pose proof (Permutation_in _ (Permutation_sym PA) H) as [<-|H']; [congruence | exact H']. }
assert (OTHER : forall k', In k' (l1 ++ l2) -> forall o, ck_beg k' <> PSec r o).
{ intros k' Hk' o Hb'. pose proof (proj1 (Forall_forall _ _) Xck k' ltac:(rewrite E; apply in_app_iff in Hk' as [?|?]; apply in_app_iff; [left|right;right]; assumption)) as [_ CK].
rewrite Hb' in CK. destruct CK as (_ & -> & _).
assert (EBB : ck_beg k' = ck_beg k) by (rewrite Hb, Hb'; reflexivity).
apply in_app_iff in Hk' as [Hk'|Hk'].
- apply (NDc (ck_beg k)); [rewrite <- EBB; apply in_map; exact Hk' | left; reflexivity].
- match goal with H : ~ In (ck_beg k) (map ck_beg l2) |- _ => apply H end. rewrite <- EBB. apply in_map. exact Hk'. }
constructor; wfr_easy_y3.
- intros c' Hc'. unfold wf_class_cf. cbn [st_cache_inited set_sec_arr set_secs set_chunks].
change (reg ?[S] c') with (reg s c'). change (cache ?[S] c') with (cache s c').
change (batch_offs ?[S] c') with (batch_offs s c').
change (chunk_offs ?[S] c') with (chunk_offs (set_chunks (l1 ++ l2) s) c'). rewrite (chunk_offs_del_sec_cf s l1 k l2 r kPage c' E Hb).
exact (Xcl c' Hc').
- cbn [st_chunks set_sec_arr set_secs set_chunks]. apply Forall_forall. intros k' Hk'.
pose proof (proj1 (Forall_forall _ _) Xck k' ltac:(rewrite E; apply in_app_iff in Hk' as [?|?]; apply in_app_iff; [left|right;right]; assumption)) as [CKn CK].
split; [exact CKn|]. cbn [st_secs set_sec_arr set_secs set_chunks].
destruct (ck_beg k') as [|b'|r' o'|c' p'] eqn:Eb'; try exact CK.
destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). split; [exact P1|]. split; [exact P2|]. exists sm'.
rewrite nth_error_lupd_other; [auto|]. intros <-. exact (OTHER k' Hk' o' Eb').
- cbn [st_chunks set_sec_arr set_secs set_chunks]. rewrite map_app. exact ND'.
- cbn [st_chunks set_sec_arr set_secs set_chunks st_nev]. rewrite E, !length_app in Xcev. rewrite length_app. cbn [length] in Xcev. lia.
- rewrite blocks_bytes_eq_cf in *. cbn [st_chunks set_sec_arr set_secs set_chunks]. rewrite E, bbytes_split_cf in Xlive. unfold is_alloc in Xlive. rewrite Hst in Xlive. lia.
- constructor; cbn [st_qthread st_qglobal st_chunks set_sec_arr set_secs set_chunks]; try assumption.
apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) Qit k' Hk') as [H1' H2']. split; [|exact H2'].
rewrite E in H1'. apply in_app_iff in H1' as [H1'|[<-|H1']]; [apply in_app_iff; left; exact H1' | exfalso | apply in_app_iff; right; exact H1'].
apply Hni. apply in_map. exact Hk'.
- constructor; cbn [st_sec_arr st_secs st_chunks st_sec_reserved set_sec_arr set_secs set_chunks].
+ exact NDA.
+ intros r'. rewrite INA, Sac, E. split.
* intros [(k' & Hk' & Hb') Hne]. exists k'. split; [|exact Hb'].
apply in_app_iff in Hk' as [Hk'|[<-|Hk']]; [apply in_app_iff; left; exact Hk' | congruence | apply in_app_iff; right; exact Hk'].
* intros (k' & Hk' & Hb'). split; [exists k'; split; [|exact Hb']|].
-- apply in_app_iff in Hk' as [Hk'|Hk']; apply in_app_iff; [left | right; right]; assumption.
-- intros ->. exact (OTHER k' Hk' kPage Hb').
+ intros r'. rewrite INA, Sal. split.
* intros [(sm' & Q1 & Q2) Hne]. exists sm'. rewrite nth_error_lupd_other by (intros ->; exact (Hne eq_refl)). auto.
* intros (sm' & Q1 & Q2). destruct (Nat.eq_dec r r') as [<-|Hne].
-- rewrite nth_error_lupd_same in Q1 by (eapply nth_error_lt; exact Hsm). injection Q1 as <-. cbn in Q2. discriminate.
-- rewrite nth_error_lupd_other in Q1 by exact Hne. split; [exists sm'; auto | intros ->; exact (Hne eq_refl)].
+ pose proof (Permutation_length PA) as L. cbn [length] in L. lia.
+ exact Sral.
+
apply Forall_lupd_cf; [exact Slen|]. cbn [sm_len]. exact (proj1 (Forall_forall _ _) Slen sm (nth_error_In _ _ Hsm)).
-
cbn [st_secs st_nev set_sec_arr set_secs set_chunks]. rewrite lupd_length. exact Xsev.
- cbn [st_sec_arr set_sec_arr set_secs set_chunks]. pose proof (Permutation_length PA) as L. cbn [length] in L. lia.
Qed.
Definition recycle_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (k : chunk) (ns : bool) (res : unit * astate) : Prop :=
let s' := snd res in
WfR_cf U pp cc bb s' /\
(exists l1 l2, st_chunks s = l1 ++ k :: l2 /\ st_chunks s' = l1 ++ l2) /\
st_qthread s' = st_qthread s /\ st_qglobal s' = st_qglobal s /\ st_nev s' = st_nev s /\ st_fs s' = st_fs s /\ st_depot s' = st_depot s /\
secs_ext s s' /\
(forall c', 0 <= c' <= 31 -> rg_alloc_user (reg s' c') = rg_alloc_user (reg s c')) /\
(forall c' y, 0 <= c' <= 31 -> In y (class_elems s' c') -> In y (class_elems s c')) /\
(forall c', 1 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s' c')) /\
(forall c', 1 <= c' <= 31 -> length (class_elems s' c') = length (class_elems s c')) /\
(st_cache_inited s = true -> st_cache_inited s' = true).
Definition recycle_postx_cf (U : Univ) (pp cc bb : Z) (s : astate) (k : chunk) (ns : bool) (res : unit * astate) : Prop :=
recycle_post_cf U pp cc bb s k ns res /\ length (st_secs (snd res)) = length (st_secs s).
Lemma recycle_chunk_okx_cf : forall U pp cc bb s k ns,
WfR_cf U pp cc bb s -> In k (st_chunks s) -> ck_state k = CQuarantined -> ~ In (ck_beg k) (map ck_beg (q_items s)) ->
atok ns (recycle_chunk k s) (recycle_postx_cf U pp cc bb s k).
Proof.
intros U pp cc bb s k ns W Hk Hst Hni.
destruct (In_split_beg _ _ Hk (wfr_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & E & N1 & N2).
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k Hk) as [CKn CK].
unfold recycle_chunk. apply atok_bind. apply atok_get. cbn [fst snd]. apply atok_bind. apply atok_mcheck; [apply mem_chunk_spec; exact Hk|].
cbn [fst snd]. apply atok_bind. apply atok_put. cbn [fst snd]. rewrite E at 1. rewrite del_chunk_present by exact N1.
destruct (ck_beg k) as [|off|r o|cc' pp'] eqn:Hb; try solve [destruct CK].
-
destruct (WfR_del_prim_cf U pp cc bb s l1 k l2 off W E Hb Hst ltac:(rewrite Hb; exact Hni)) as (W1 & G1 & G2 & G3 & G4 & G5). cbv zeta in *.
eapply atok_mono; [|apply (cache_dealloc_ok_cf U pp cc bb (set_chunks (l1 ++ l2) s) (prim_class off) off ns W1 ltac:(lia) G2 G3 G4)].
intros ns' [[] s'] (W' & RO' & HI' & AU' & CE' & MF' & LEN'). cbn [snd] in *.
destruct RO' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). cbn in R1, R2, R3, R4, R5, R6, R7, R8, R9, R10.
unfold recycle_postx_cf, recycle_post_cf. cbn [snd]. split; [|rewrite R2; reflexivity]. splits; try assumption.
+ exists l1, l2. auto.
+ intros r0 sm0 E0. exists sm0. rewrite R2. auto.
+ intros c' y Hc' Hy. destruct (CE' c' y Hc' Hy) as [[-> ->]|Hy'].
* unfold class_elems. rewrite !in_app_iff. right. right. left. apply (In_chunk_offs s k off Hk Hb).
* exact (G5 c' y Hy').
+ intros c' Hc'. exact (MF' c' ltac:(lia)).
+ intros c' Hc'. rewrite (LEN' c') by lia. pose proof (Permutation_length (class_elems_del_cf s l1 k l2 c' E)) as L.
rewrite length_app, chunk_offs_one_cf, Hb in L.
destruct (Z.eqb_spec c' (prim_class off)) as [->|Hne].
* rewrite Z.eqb_refl in L. cbn [length] in L. lia.
* replace (prim_class off =? c') with false in L by (symmetry; apply Z.eqb_neq; lia). cbn [length] in L. lia.
+ intros _. exact HI'.
-
destruct CK as (P1 & -> & sm & Hsm & Hlive & Hsz & Hlen).
pose proof (wfr_secondary _ _ _ _ _ W) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (Hr : In r (st_sec_arr s)) by (apply Sac; exists k; auto).
destruct (index_of_spec_cf (st_sec_arr s) r 0%nat Hr) as (i & Ei & Hi). rewrite Nat.add_0_l in Ei.
unfold sec_dealloc. apply atok_bind. apply atok_get. cbn [fst snd st_secs st_sec_arr set_chunks]. rewrite Hsm, Ei.
set (s1 := set_chunks (l1 ++ l2) s).
assert (TAIL : forall ns1, atok ns1
((_ <- askz (KMunmapSec r (sm_len sm)) ;;
modify (fun s0 => set_sec_arr (removelast (lupd (st_sec_arr s0) i (last (st_sec_arr s0) r)))
(set_secs (lupd (st_secs s0) r (mkSec (sm_len sm) (sm_size sm) false)) s0))) s1)
(recycle_postx_cf U pp cc bb s k)).
{ intros ns1. apply atok_bind. apply atok_askz.
- cbn. split; [exact Hr | exists sm; auto].
- intros z Hz. cbn [fst snd progz]. apply atok_modify. unfold recycle_postx_cf, recycle_post_cf. cbn [snd]. subst s1.
cbn [st_sec_arr st_secs set_chunks st_qthread st_qglobal st_nev st_fs st_depot set_sec_arr set_secs].
split; [|apply lupd_length]. splits; try reflexivity.
+ apply (WfR_del_sec_cf U pp cc bb s l1 k l2 r sm i W E Hb Hst ltac:(rewrite Hb; exact Hni) Hsm Hi).
+ exists l1, l2. auto.
+ intros r0 sm0 E0. cbn [st_secs set_sec_arr set_secs set_chunks]. destruct (Nat.eq_dec r r0) as [<-|Hne].
* rewrite Hsm in E0. injection E0 as <-. exists (mkSec (sm_len sm) (sm_size sm) false).
rewrite nth_error_lupd_same by (eapply nth_error_lt; exact Hsm). cbn. auto.
* exists sm0. rewrite nth_error_lupd_other by exact Hne. auto.
+ intros c' y Hc' Hy. unfold class_elems in Hy |- *.
change (reg ?[S] c') with (reg s c') in Hy. change (cache ?[S] c') with (cache s c') in Hy. change (batch_offs ?[S] c') with (batch_offs s c') in Hy.
change (chunk_offs ?[S] c') with (chunk_offs (set_chunks (l1 ++ l2) s) c') in Hy. rewrite (chunk_offs_del_sec_cf s l1 k l2 r kPage c' E Hb) in Hy. exact Hy.
+ intros c' Hc'. match goal with |- length (class_elems ?S2 _) = _ =>
unfold class_elems; change (reg S2 c') with (reg s c'); change (cache S2 c') with (cache s c');
change (batch_offs S2 c') with (batch_offs s c'); change (chunk_offs S2 c') with (chunk_offs (set_chunks (l1 ++ l2) s) c') end.
rewrite (chunk_offs_del_sec_cf s l1 k l2 r kPage c' E Hb). reflexivity.
+ intros Hi0. exact Hi0. }
destruct (needs_remap (sm_len sm)) eqn:NR.
+ apply atok_bind. apply atok_bind. apply atok_askz.
* cbn -[Z.le Z.div Z.add Z.modulo kClearShadowMmapThreshold Z.mul]. unfold needs_remap in NR. apply Z.leb_le in NR.
split; [exact NR|]. exists r, 0, sm. subst s1. cbn [st_secs set_chunks]. splits; auto; try lia; reflexivity.
* intros z Hz. cbn in Hz. cbn [fst snd]. unfold aGranted. destruct (Z.eqb_spec z 1) as [->|Hne].
-- cbn [progz Z.eqb Pos.eqb]. apply atok_ret. apply TAIL.
-- replace (progz _ z) with false by (cbn; destruct Hz as [->| ->]; cbn; congruence). apply atok_spin.
+ apply atok_bind. apply atok_ret. apply TAIL.
Qed.
Lemma recycle_chunk_ok_cf : forall U pp cc bb s k ns,
WfR_cf U pp cc bb s -> In k (st_chunks s) -> ck_state k = CQuarantined -> ~ In (ck_beg k) (map ck_beg (q_items s)) ->
atok ns (recycle_chunk k s) (recycle_post_cf U pp cc bb s k).
Proof.
intros U pp cc bb s k ns W Hk Hst Hni. eapply atok_mono; [|exact (recycle_chunk_okx_cf U pp cc bb s k ns W Hk Hst Hni)]. intros b r (H & _). exact H.
Qed.
Lemma fframe_refl_cf : forall s, fframe_cf s s.
Proof. intros s. unfold fframe_cf. splits; try reflexivity. apply secs_ext_refl. Qed.
Lemma fframe_trans_cf : forall s1 s2 s3, fframe_cf s1 s2 -> fframe_cf s2 s3 -> fframe_cf s1 s3.
Proof.
intros s1 s2 s3 (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold fframe_cf.
rewrite B1, B2, B3, B4. splits; try assumption. eapply secs_ext_trans; eassumption.
Qed.
Lemma blocks_del_quar_cf : forall s s' l1 k l2, st_chunks s = l1 ++ k :: l2 -> st_chunks s' = l1 ++ l2 -> ck_state k = CQuarantined ->
blocks s' = blocks s.
Proof.
intros s s' l1 k l2 E E' Hst. unfold blocks. rewrite E, E', !filter_app. cbn [filter].
replace (is_alloc k) with false by (unfold is_alloc; rewrite Hst; reflexivity). reflexivity.
Qed.
Lemma recycle_post_fframe_cf : forall U pp cc bb s k ns r, ck_state k = CQuarantined -> recycle_post_cf U pp cc bb s k ns r -> fframe_cf s (snd r).
Proof.
intros U pp cc bb s k ns [u s'] Hst (W' & (l1 & l2 & E & E') & Rqt & Rqg & Rnev & Rfs & Rdep & SE & _). cbn [snd] in *.
unfold fframe_cf. splits; try assumption. eapply blocks_del_quar_cf; eassumption.
Qed.
Definition RIx_cf (U : Univ) (pp cc bb : Z) (s : astate) (its : list chunk) (P : list batch) (selfs : list Z) : Prop :=
WfR_cf U pp cc bb s /\
Forall (fun k => In k (st_chunks s) /\ ck_state k = CQuarantined) (its ++ flat_map b_items P) /\
NoDup (map ck_beg ((its ++ flat_map b_items P) ++ q_items s)) /\
Forall (fun b => (length (b_items b) <= Z.to_nat kBatchSlots)%nat) P /\
Forall (fun z => 0 <= z - region_off kBatchClass < rg_alloc_user (reg s kBatchClass) /\
(z - region_off kBatchClass) mod class_size kBatchClass = 0 /\
~ In (z - region_off kBatchClass) (class_elems s kBatchClass)) (selfs ++ map b_self P) /\
NoDup (selfs ++ map b_self P).
Lemma RI_RIx_cf : forall U pp cc bb s P, RI_cf U pp cc bb s P -> RIx_cf U pp cc bb s [] P [].
Proof.
intros U pp cc bb s P (A1 & A2 & A3 & A4 & A5 & A6). unfold RIx_cf. cbn [app]. splits; try assumption.
- apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb). exact (proj1 (Forall_forall _ _) A5 b Hb).
Qed.
Definition xfr_cf (s s' : astate) (d : Z -> Z) : Prop :=
(forall c', 1 <= c' <= 31 -> rg_alloc_user (reg s' c') = rg_alloc_user (reg s c')) /\
(forall c', 1 <= c' <= 31 -> rg_mapped_fa (reg s c') <= rg_mapped_fa (reg s' c')) /\
(forall c', 1 <= c' <= 31 -> Z.of_nat (length (class_elems s' c')) = Z.of_nat (length (class_elems s c')) + d c') /\
(Z.of_nat (length (st_chunks s')) <= Z.of_nat (length (st_chunks s)) /\ crw (st_chunks s') <= crw (st_chunks s) /\
length (st_secs s') = length (st_secs s) /\ Z.of_nat (length (all_batches s')) <= Z.of_nat (length (all_batches s))).
Lemma xfr_refl_cf : forall s, xfr_cf s s (fun _ => 0).
Proof. intros s. unfold xfr_cf. splits; intros; lia. Qed.
Lemma xfr_trans_cf : forall s1 s2 s3 d1 d2 d, xfr_cf s1 s2 d1 -> xfr_cf s2 s3 d2 -> (forall c', 1 <= c' <= 31 -> d c' = d1 c' + d2 c') -> xfr_cf s1 s3 d.
Proof.
intros s1 s2 s3 d1 d2 d (A1 & M1 & L1 & K1 & C1 & S1 & B1) (A2 & M2 & L2 & K2 & C2 & S2 & B2) E. unfold xfr_cf. splits; try lia; intros c' Hc'.
- rewrite (A2 c' Hc'). exact (A1 c' Hc').
- pose proof (M1 c' Hc'). pose proof (M2 c' Hc'). lia.
- rewrite (L2 c' Hc'), (L1 c' Hc'), (E c' Hc'). lia.
Qed.
Lemma xfr_cdef_cf : forall s s' d, xfr_cf s s' d -> forall c', 1 <= c' <= 31 -> cdef s' c' = cdef s c' - class_size c' * d c'.
Proof. intros s s' d (A & _ & L & _) c' Hc'. unfold cdef. rewrite (A c' Hc'), (L c' Hc'). lia. Qed.
Lemma recycle_post_xfr_cf : forall U pp cc bb s k ns r, recycle_postx_cf U pp cc bb s k ns r -> xfr_cf s (snd r) (fun _ => 0).
Proof.
intros U pp cc bb s k ns r ((_ & (l1 & l2 & E & E') & Rqt & Rqg & _ & _ & _ & _ & AU & _ & MF & LEN & _) & RS). unfold xfr_cf. splits; try (intros c' Hc').
- apply AU. lia.
- apply MF. exact Hc'.
- rewrite (LEN c' Hc'). lia.
- rewrite E, E', !length_app. cbn [length]. lia.
- rewrite E, E', !crw_app. change (crw (k :: l2)) with (cw k + crw l2). pose proof (cw_nonneg k). lia.
- exact RS.
- unfold all_batches. rewrite Rqt, Rqg. lia.
Qed.
Lemma cache_dealloc_post_xfr_cf : forall U pp cc bb s c x ns r, cache_dealloc_post_cf U pp cc bb s c x ns r ->
xfr_cf s (snd r) (fun c' => if c' =? c then 1 else 0).
Proof.
intros U pp cc bb s c x ns r (_ & (R1 & R2 & _ & _ & R5 & R6 & _) & _ & AU & _ & MF & LEN). unfold xfr_cf. splits; try (intros c' Hc').
- apply AU. lia.
- apply MF. lia.
- rewrite (LEN c' ltac:(lia)). destruct (c' =? c); lia.
- rewrite R1. lia.
- rewrite R1. lia.
- rewrite R2. reflexivity.
- unfold all_batches. rewrite R5, R6. lia.
Qed.
Lemma recycle_items_okx_cf : forall U pp cc bb its, forall s P selfs ns fuel,
RIx_cf U pp cc bb s its P selfs -> (length its <= fuel)%nat ->
atok ns (recycle_items fuel its s)
(fun ns' res => (RIx_cf U pp cc bb (snd res) [] P selfs /\ fframe_cf s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq_cf (snd res) = unq_cf s - items_n its) /\
xfr_cf s (snd res) (fun _ => 0)).
Proof.
intros U pp cc bb its. induction its as [|k its IH]; intros s P selfs ns fuel RX Hfuel.
- destruct fuel; cbn [recycle_items]; apply atok_ret; cbn [snd]; (split; [|apply xfr_refl_cf]); (split; [exact RX | split; [apply fframe_refl_cf | rewrite items_n_nil_cf; splits; [reflexivity | reflexivity | lia]]]).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [recycle_items]. apply atok_bind.
destruct RX as (W & IT & ND & BL & SF & NDS).
inversion IT as [|k0 rest [Hk Hst] ITr]; subst.
assert (Hni : ~ In (ck_beg k) (map ck_beg (q_items s))).
{ cbn [app map] in ND. inversion ND; subst. intros Hin. match goal with H : ~ In (ck_beg k) _ |- _ => apply H end.
rewrite map_app. apply in_app_iff. right. exact Hin. }
eapply atok_mono; [|apply (recycle_chunk_okx_cf U pp cc bb s k ns W Hk Hst Hni)].
intros ns1 [[] s1] RPX. pose proof (recycle_post_xfr_cf _ _ _ _ _ _ _ _ RPX) as XF1. destruct RPX as [RP _].
pose proof (recycle_post_fframe_cf U pp cc bb s k ns1 _ Hst RP) as FF.
unfold recycle_post_cf in RP. cbn [fst snd] in FF, RP, XF1 |- *.
destruct RP as (W1 & (l1 & l2 & E & E1) & Rqt & Rqg & Rnev & Rfs & Rdep & SE & AU & CE & MF & LEN & HI1).
assert (EQI : q_items s1 = q_items s) by (unfold q_items, all_batches; rewrite Rqt, Rqg; reflexivity).
pose proof (unq_del_cf s s1 l1 k l2 E E1 Hst Rqt Rqg) as UQ1.
eapply atok_mono; [|apply (IH s1 P selfs ns1 f); [|cbn in Hfuel; lia]].
{ intros b [u s2] ((RX2 & FF2 & Q2 & G2 & U2) & XF2). cbn [snd] in Q2, G2, U2, XF2 |- *.
split; [|eapply xfr_trans_cf; [exact XF1 | exact XF2 | intros; lia]].
split; [exact RX2 | split; [eapply fframe_trans_cf; [exact FF | exact FF2]|]].
rewrite Q2, G2, U2, UQ1, Rqt, Rqg, items_n_cons_cf. splits; [reflexivity | reflexivity | lia]. }
cbn [app map] in ND. inversion ND as [|b0 rest0 Hnk NDr]; subst.
unfold RIx_cf. splits.
+ exact W1.
+ apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) ITr k' Hk') as [H1 H2]. split; [|exact H2].
rewrite E1. rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply in_app_iff; left; exact H1 | exfalso | apply in_app_iff; right; exact H1].
apply Hnk. rewrite map_app. apply in_app_iff. left. apply in_map. exact Hk'.
+ rewrite EQI. exact NDr.
+ exact BL.
+ eapply Forall_impl; [|exact SF]. cbv beta. intros z (Z1 & Z2 & Z3). rewrite AU by (unfold kBatchClass; lia).
split; [exact Z1 | split; [exact Z2|]]. intros Hin. exact (Z3 (CE kBatchClass _ ltac:(unfold kBatchClass; lia) Hin)).
+ exact NDS.
Qed.
Lemma recycle_items_ok_cf : forall U pp cc bb its, forall s P selfs ns fuel,
RIx_cf U pp cc bb s its P selfs -> (length its <= fuel)%nat ->
atok ns (recycle_items fuel its s)
(fun ns' res => RIx_cf U pp cc bb (snd res) [] P selfs /\ fframe_cf s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq_cf (snd res) = unq_cf s - items_n its).
Proof.
intros U pp cc bb its s P selfs ns fuel RX Hfuel.
eapply atok_mono; [|exact (recycle_items_okx_cf U pp cc bb its s P selfs ns fuel RX Hfuel)]. intros b r (H & _). exact H.
Qed.
Lemma cache_dealloc_post_fframe_cf : forall U pp cc bb s c x ns r, cache_dealloc_post_cf U pp cc bb s c x ns r -> fframe_cf s (snd r).
Proof.
intros U pp cc bb s c x ns [u s'] (W' & RO & _ & _). cbn [snd] in *.
destruct RO as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10). unfold fframe_cf. splits; try assumption.
- unfold blocks. rewrite R1. reflexivity.
- intros r0 sm0 E0. exists sm0. rewrite R2. auto.
Qed.
Lemma do_recycle_okx_cf : forall U pp cc bb P, forall s ns fuel,
RIx_cf U pp cc bb s [] P [] -> (length P <= fuel)%nat ->
atok ns (do_recycle fuel P s) (fun ns' res => (WfR_cf U pp cc bb (snd res) /\ fframe_cf s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq_cf (snd res) = unq_cf s - items_n (flat_map b_items P)) /\
xfr_cf s (snd res) (fun c' => if c' =? kBatchClass then Z.of_nat (length P) else 0)).
Proof.
intros U pp cc bb P. induction P as [|b P IH]; intros s ns fuel RX Hfuel.
- destruct fuel; cbn [do_recycle flat_map]; apply atok_ret; cbn [snd]; (split; [|eapply xfr_trans_cf; [apply xfr_refl_cf | apply xfr_refl_cf | intros c' _; cbn [length]; destruct (c' =? kBatchClass); reflexivity]]);
(split; [exact (proj1 RX) | split; [apply fframe_refl_cf | rewrite items_n_nil_cf; splits; [reflexivity | reflexivity | lia]]]).
- destruct fuel as [|f]; [cbn in Hfuel; lia|]. cbn [do_recycle]. apply atok_bind.
destruct RX as (W & IT & ND & BL & SF & NDS). cbn [app flat_map map] in IT, ND, SF, NDS.
inversion BL as [|b0 P0 BLb BLP]; subst.
eapply atok_mono; [|apply (recycle_items_okx_cf U pp cc bb (b_items b) s P [b_self b] ns 1100)].
2:{ unfold RIx_cf. cbn [app]. splits; try assumption. }
2:{ unfold kBatchSlots in BLb. lia. }
intros ns1 [[] s1] ((RX1 & FF1 & TQ1 & TG1 & UQ1) & XF1). cbn [fst snd] in TQ1, TG1, UQ1, XF1 |- *. apply atok_bind.
destruct RX1 as (W1 & IT1 & ND1 & BL1 & SF1 & NDS1). cbn [app] in IT1, ND1. cbn [fst snd] in SF1.
inversion SF1 as [|z0 l0 (Z1 & Z2 & Z3) SFP]; subst. inversion NDS1 as [|z1 l1 Hnself NDSP]; subst.
eapply atok_mono; [|apply (cache_dealloc_ok_cf U pp cc bb s1 kBatchClass (b_self b) ns1 W1 ltac:(unfold kBatchClass; lia) Z1 Z2 Z3)].
intros ns2 [[] s2] CP. pose proof (cache_dealloc_post_fframe_cf _ _ _ _ _ _ _ _ _ CP) as FF2. pose proof (cache_dealloc_post_xfr_cf _ _ _ _ _ _ _ _ _ CP) as XF2. cbn [fst snd] in FF2, XF2 |- *.
destruct CP as (W2 & RO2 & HI2 & AU2 & CE2 & MF2 & LEN2). cbn [snd] in W2, RO2, HI2, AU2, CE2, MF2, LEN2.
destruct RO2 as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
pose proof (unq_same_cf s1 s2 R1 R5 R6) as UQ2.
eapply atok_mono; [|apply (IH s2 ns2 f); [|cbn in Hfuel; lia]].
{ intros b' [u s3] ((W3 & FF3 & TQ3 & TG3 & UQ3) & XF3). cbn [snd] in TQ3, TG3, UQ3, XF3 |- *.
split; [|eapply xfr_trans_cf; [exact XF1 | eapply xfr_trans_cf; [exact XF2 | exact XF3 | intros; reflexivity] |]].
2:{ intros c' _. cbn beta. cbn [length]. rewrite Nat2Z.inj_succ. destruct (c' =? kBatchClass); lia. }
split; [exact W3 | split; [eapply fframe_trans_cf; [exact FF1 | eapply fframe_trans_cf; [exact FF2 | exact FF3]]|]].
rewrite TQ3, TG3, UQ3, R5, R6, TQ1, TG1, UQ2, UQ1. cbn [flat_map]. rewrite items_n_app. splits; [reflexivity | reflexivity | lia]. }
unfold RIx_cf. cbn [app]. splits.
+ exact W2.
+ rewrite R1. exact IT1.
+ replace (q_items s2) with (q_items s1) by (unfold q_items, all_batches; rewrite R5, R6; reflexivity). exact ND1.
+ exact BLP.
+ apply Forall_forall. intros z Hz. pose proof (proj1 (Forall_forall _ _) SFP z Hz) as (Y1 & Y2 & Y3).
rewrite AU2 by (unfold kBatchClass; lia). split; [exact Y1 | split; [exact Y2|]].
intros Hin. destruct (CE2 kBatchClass _ ltac:(unfold kBatchClass; lia) Hin) as [[Ez _]|Hin'].
* apply Hnself. replace (b_self b) with z by lia. exact Hz.
* exact (Y3 Hin').
+ exact NDSP.
Qed.
Lemma do_recycle_ok_cf : forall U pp cc bb P, forall s ns fuel,
RIx_cf U pp cc bb s [] P [] -> (length P <= fuel)%nat ->
atok ns (do_recycle fuel P s) (fun ns' res => WfR_cf U pp cc bb (snd res) /\ fframe_cf s (snd res) /\
st_qthread (snd res) = st_qthread s /\ st_qglobal (snd res) = st_qglobal s /\ unq_cf (snd res) = unq_cf s - items_n (flat_map b_items P)).
Proof.
intros U pp cc bb P s ns fuel RX Hfuel.
eapply atok_mono; [|exact (do_recycle_okx_cf U pp cc bb P s ns fuel RX Hfuel)]. intros b r (H & _). exact H.
Qed.
Lemma of_nat_100000_cf : Z.of_nat 100000%nat = 100000.
Proof. vm_compute. reflexivity. Qed.
Lemma xfr_transfer_cf : forall s,
xfr_cf s (set_qglobal (mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s))) (set_qthread qc0 s)) (fun _ => 0).
Proof.
intros s. unfold xfr_cf. splits; try (intros c' Hc'); [reflexivity | apply Z.le_refl | | apply Z.le_refl | apply Z.le_refl | reflexivity |].
- unfold class_elems. match goal with |- context [reg ?S c'] => change (reg S c') with (reg s c'); change (cache S c') with (cache s c'); change (chunk_offs S c') with (chunk_offs s c') end.
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 app].
destruct (c' =? kBatchClass); [|lia]. rewrite !length_app, !length_map, !length_app. lia.
- unfold all_batches. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 app]. rewrite !length_app. lia.
Qed.
Lemma xfr_pop_cf : forall s P rest bytes, qc_list (st_qglobal s) = P ++ rest ->
xfr_cf s (set_qglobal (mkQC rest bytes) s) (fun c' => if c' =? kBatchClass then - Z.of_nat (length P) else 0).
Proof.
intros s P rest bytes EL. unfold xfr_cf. splits; try (intros c' Hc'); [reflexivity | apply Z.le_refl | | apply Z.le_refl | apply Z.le_refl | reflexivity |].
- unfold class_elems. match goal with |- context [reg ?S c'] => change (reg S c') with (reg s c'); change (cache S c') with (cache s c'); change (chunk_offs S c') with (chunk_offs s c') end.
unfold batch_offs, all_batches. cbn [st_qthread st_qglobal set_qglobal qc_list]. rewrite EL.
destruct (c' =? kBatchClass); [|lia]. rewrite !length_app, !length_map, !length_app, !Nat2Z.inj_add. lia.
- unfold all_batches. cbn [st_qthread st_qglobal set_qglobal qc_list]. rewrite EL, !length_app. lia.
Qed.
Lemma maybe_drain_okx_cf : forall U pp cc bb s ns,
WfR_cf U pp cc bb s ->
(kQuarantineCacheMax < qc_bytes (st_qthread s) -> kQuarantineMax < qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) ->
Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s))) < 100000 /\
2 * (kBatchBytes * Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s)))) <= qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)) ->
atok ns (maybe_drain s) (fun ns' res => (WfR_cf U pp cc bb (snd res) /\ fframe_cf s (snd res) /\
qc_bytes (st_qthread (snd res)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (snd res)) <= Z.max (qc_bytes (st_qglobal s)) kQuarantineMax /\
unq_cf (snd res) = unq_cf s) /\ xfr_cf s (snd res) (fun _ => 0)).
Proof.
intros U pp cc bb s ns W HB4.
unfold maybe_drain. apply atok_bind. apply atok_get. cbn [fst snd].
destruct (qc_bytes (st_qthread s) <=? kQuarantineCacheMax) eqn:E1.
{ apply atok_ret. apply Z.leb_le in E1. cbn [snd]. split; [|apply xfr_refl_cf]. splits; [exact W | apply fframe_refl_cf | exact E1 | lia | reflexivity]. }
apply atok_bind. apply atok_put. cbn [fst snd].
pose proof (WfR_transfer_cf U pp cc bb s W ltac:(apply Z.leb_gt; exact E1)) as WT. cbv zeta in WT. set (sT := set_qglobal _ _) in *.
assert (FFT : fframe_cf s sT).
{ subst sT. unfold fframe_cf. cbn [st_nev st_fs st_depot set_qglobal set_qthread]. splits; try reflexivity. intros r0 sm0 E0; exists sm0; auto. }
pose proof (unq_transfer_cf s) as UQT. fold sT in UQT.
pose proof (xfr_transfer_cf s) as XFT. fold sT in XFT.
match goal with |- atok _ ((if ?b then _ else _) _) _ => destruct b eqn:E2 end.
{ apply atok_ret. apply Z.leb_le in E2. cbn [snd]. split; [|exact XFT]. splits; [exact WT | exact FFT | subst sT; cbn; kc; lia | subst sT; cbn [st_qglobal set_qglobal set_qthread] in E2 |- *; lia | exact UQT]. }
apply Z.leb_gt in E2. cbn [qc_bytes] in E2.
assert (BB : Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s))) < 100000 /\
2 * (kBatchBytes * Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s)))) <= qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)).
{ apply HB4; [apply Z.leb_gt; exact E1 | exact E2]. }
apply atok_bind. apply atok_mcheck.
{ apply Z.leb_le. subst sT. cbn [st_qglobal set_qglobal set_qthread qc_list qc_bytes]. exact (proj2 BB). }
cbn [fst snd]. destruct (pop_batches _ _ _) as [g' popped] eqn:EP. pose proof EP as EP0.
apply pop_batches_spec_cf in EP as (P & -> & EL & EB). cbn [rev app qc_list qc_bytes] in EL, EB |- *.
apply atok_bind. apply atok_modify. cbn [fst snd].
assert (EG : g' = mkQC (qc_list g') (qc_bytes (st_qglobal sT) - sum_bytes P)) by (destruct g'; cbn in EB |- *; rewrite EB; reflexivity).
pose proof (RI_pop_cf U pp cc bb sT P (qc_list g') WT EL) as RI0. rewrite <- EG in RI0.
assert (FFP : fframe_cf sT (set_qglobal g' sT)).
{ unfold fframe_cf. cbn [st_nev st_fs st_depot set_qglobal]. splits; try reflexivity. intros r0 sm0 E0; exists sm0; auto. }
assert (L : (length P <= length (qc_list (st_qglobal s) ++ qc_list (st_qthread s)))%nat) by (rewrite EL, length_app; lia).
assert (GB : qc_bytes g' <= kQuarantineMax).
{ destruct (pop_batches_stop_cf _ _ _ _ _ EP0) as [Hmin|Hnil].
- cbn [qc_list]. apply Nat2Z.inj_lt. rewrite of_nat_100000_cf. exact (proj1 BB).
- kc. lia.
- rewrite EB. pose proof (wq_bytes_g _ (wfr_quarantine _ _ _ _ _ WT)) as QB. subst sT. cbn [st_qglobal set_qglobal set_qthread qc_bytes qc_list] in QB, EL |- *.
rewrite QB, EL, Hnil, sum_bytes_app_cf. cbn. kc. lia. }
pose proof (unq_pop_cf sT P (qc_list g') (qc_bytes (st_qglobal sT) - sum_bytes P) EL) as UQP. rewrite <- EG in UQP.
pose proof (xfr_pop_cf sT P (qc_list g') (qc_bytes g') EL) as XFP. replace (mkQC (qc_list g') (qc_bytes g')) with g' in XFP by (destruct g'; reflexivity).
eapply atok_mono; [|apply (do_recycle_okx_cf U pp cc bb P (set_qglobal g' sT) _ 100000%nat (RI_RIx_cf _ _ _ _ _ _ RI0))].
- intros b [u s'] ((W' & FF' & TQ' & TG' & UQ') & XF'). cbn [snd] in TQ', TG', UQ', XF' |- *.
split; [|eapply xfr_trans_cf; [exact XFT | eapply xfr_trans_cf; [exact XFP | exact XF' | intros; reflexivity] | intros c' _; cbn beta; destruct (c' =? kBatchClass); lia]].
split; [exact W' | split; [eapply fframe_trans_cf; [exact FFT | eapply fframe_trans_cf; [exact FFP | exact FF']]|]].
rewrite TQ', TG', UQ', UQP, UQT. subst sT. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_bytes qc0]. splits; [kc; lia | lia | lia].
- apply Nat2Z.inj_le. rewrite of_nat_100000_cf. pose proof (proj1 BB). lia.
Qed.
Lemma maybe_drain_ok_cf : forall U pp cc bb s ns,
WfR_cf U pp cc bb s ->
(kQuarantineCacheMax < qc_bytes (st_qthread s) -> kQuarantineMax < qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) ->
Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s))) < 100000 /\
2 * (kBatchBytes * Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s)))) <= qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)) ->
atok ns (maybe_drain s) (fun ns' res => WfR_cf U pp cc bb (snd res) /\ fframe_cf s (snd res) /\
qc_bytes (st_qthread (snd res)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (snd res)) <= Z.max (qc_bytes (st_qglobal s)) kQuarantineMax /\
unq_cf (snd res) = unq_cf s).
Proof.
intros U pp cc bb s ns W HB4. eapply atok_mono; [|exact (maybe_drain_okx_cf U pp cc bb s ns W HB4)]. intros b r (H & _). exact H.
Qed.

(* ---------------------------------------------------------------------------- *)
(* The drain at WfP_cf, wherever the merge-free shape holds (the plug for        *)
(* drain_spec_cf: Compl0 survives because the drain's cdef delta is 0).          *)
Lemma maybe_drain_okp_cf : forall U pp cc bb s ns,
WfP_cf U pp cc bb s ->
(kQuarantineCacheMax < qc_bytes (st_qthread s) -> kQuarantineMax < qc_bytes (st_qglobal s) + qc_bytes (st_qthread s) ->
Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s))) < 100000 /\
2 * (kBatchBytes * Z.of_nat (length (qc_list (st_qglobal s) ++ qc_list (st_qthread s)))) <= qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)) ->
atok ns (maybe_drain s) (fun ns' res => WfP_cf U pp cc bb (snd res) /\ fframe_cf s (snd res) /\
qc_bytes (st_qthread (snd res)) <= kQuarantineCacheMax /\
qc_bytes (st_qglobal (snd res)) <= Z.max (qc_bytes (st_qglobal s)) kQuarantineMax /\ unq_cf (snd res) = unq_cf s).
Proof.
intros U pp cc bb s ns W HB4.
eapply atok_mono; [|exact (maybe_drain_okx_cf U pp cc bb s ns (WfR_of_WfP_cf _ _ _ _ _ W) HB4)].
intros b r ((W' & F' & T' & G' & Q') & XF). splits; try assumption.
apply WfP_of_WfR_cf; [exact W'|]. intros c Hc. rewrite (xfr_cdef_cf _ _ _ XF c Hc), (wfc_compl0 _ _ _ _ _ W c Hc). lia.
Qed.

Lemma WfP_cf_set_internal_inited_cf : forall U pp cc bb s v, WfP_cf U pp cc bb s -> WfP_cf U pp cc bb (set_internal_inited v s).
Proof.
intros U pp cc bb s v W. apply WfP_of_WfR_cf; [|exact (wfc_compl0 _ _ _ _ _ W)].
apply WfR_set_internal_inited_cf. exact (WfR_of_WfP_cf _ _ _ _ _ W).
Qed.

(* ---------------------------------------------------------------------------- *)
(* free, YG03.v:1308-1431, for every drain md that meets drain_spec_cf.         *)
(* The universe premise is a Section Hypothesis, as cgif's model_laws_ok         *)
(* (YG05.v:139) takes it.                                                        *)
Section FREE.
Variable U : Univ.
Hypothesis HU : universe_ok U.
Variable md : M unit.
Hypothesis md_ok : drain_spec_cf U md.

Theorem free_gen_cf : forall s p n tr,
Wf_cf U s -> batch_room_cf s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok true (free_with_cf md p tr s) (free_post_ycf U s p n).
Proof.
intros s p n tr W Hroom Hp Htr.
pose proof (WfP_cf_tick_y3 U s W) as W1. set (s1 := set_nev (st_nev s + 1) s) in *.
unfold free_with_cf. apply atok_bind. apply atok_tick. cbn [fst snd]. fold s1.
apply atok_bind. apply atok_get. cbn [fst snd].
assert (K : forall v, let s2 := set_internal_inited v s1 in WfP_cf U 1 1 1 s2 ->
atok true
(match p with
| PNull => ret tt
| _ => s0 <- get ;;
match find_user (st_chunks s0) p with
| Some k =>
(if match ck_state k with CAllocated => true | CQuarantined => false end then ret tt else fail (FModel 12)) ;;
depot_put tr ;;
modify (fun s3 => set_chunks (upd_chunk (st_chunks s3) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) s3) ;;
(if ck_n (mkChunk (ck_beg k) (ck_req k) CQuarantined) <=? kQuarantineMax then enqueue (mkChunk (ck_beg k) (ck_req k) CQuarantined)
 else recycle_chunk (mkChunk (ck_beg k) (ck_req k) CQuarantined)) ;;
md
| None => fail (FModel 11)
end
end s2) (free_post_ycf U s p n)).
2:{ apply atok_bind. destruct (st_internal_inited s1) eqn:Ei.
- apply atok_ret. cbn [fst snd]. replace s1 with (set_internal_inited true s1) by (subst s1; destruct s; cbn in Ei |- *; subst; reflexivity).
apply K. apply WfP_cf_set_internal_inited_cf. exact W1.
- apply atok_modify. cbn [fst snd]. apply K. apply WfP_cf_set_internal_inited_cf. exact W1. }
intros v s2 W2.
assert (F2 : st_chunks s2 = st_chunks s /\ st_secs s2 = st_secs s /\ st_fs s2 = st_fs s /\ st_depot s2 = st_depot s /\
st_nev s2 = st_nev s + 1 /\ q_items s2 = q_items s /\ blocks s2 = blocks s) by (subst s2 s1; repeat split; reflexivity).
destruct F2 as (Fck & Fsecs & Ffs & Fdep & Fnev & Fqi & Fbl).
assert (MAIN : forall q, In (q, n) (blocks s) ->
atok true ((s0 <- get ;;
match find_user (st_chunks s0) q with
| Some k =>
(if match ck_state k with CAllocated => true | CQuarantined => false end then ret tt else fail (FModel 12)) ;;
depot_put tr ;;
modify (fun s3 => set_chunks (upd_chunk (st_chunks s3) (mkChunk (ck_beg k) (ck_req k) CQuarantined)) s3) ;;
(if ck_n (mkChunk (ck_beg k) (ck_req k) CQuarantined) <=? kQuarantineMax then enqueue (mkChunk (ck_beg k) (ck_req k) CQuarantined)
 else recycle_chunk (mkChunk (ck_beg k) (ck_req k) CQuarantined)) ;;
md
| None => fail (FModel 11)
end) s2) (free_post_ycf U s q n)).
2:{ destruct p as [|po|pr poff|pc ppos]; [| apply MAIN | apply MAIN | apply MAIN]; try (destruct Hp as [Hp|Hp]; [discriminate | exact Hp]).
apply atok_ret. unfold free_post_ycf. cbn [snd]. pose proof (wfc_slack _ _ _ _ _ W2).
splits; [unfold Wf_cf; eapply WfP_cf_weaken; [exact W2|lia|lia|lia] | exact Fnev | intros r0 sm0 E0; exists sm0; rewrite Fsecs; auto | unfold frames; rewrite Ffs; reflexivity | |].
- exists [], (blocks s). cbn [app]. split; [left; auto | exact Fbl].
- intros QT. apply (qtight_ext s); [exact Fck | subst s2 s1; reflexivity | subst s2 s1; reflexivity | exact QT]. }
intros q Hq. apply atok_bind. apply atok_get. cbn [fst snd].
pose proof (WfR_of_WfP_cf _ _ _ _ _ W2) as W2r.
destruct (find_user_block_cf U 1 1 1 s2 q n W2r ltac:(rewrite Fbl; exact Hq)) as (k & -> & Hk & Hst & Hu & Hr).
apply atok_bind. apply atok_if; intros Hb; [apply atok_ret | rewrite Hst in Hb; discriminate]. cbn [fst snd].
apply atok_bind. eapply atok_mono; [|apply (depot_put_ok U s2 tr true); [rewrite Fdep; exact (wfc_depot _ _ _ _ _ W) | exact HU | exact (admits_keep U tr s s2 Htr (or_introl Fdep))]].
intros ns3 [[] s3] (d & -> & Hdf & Hd & ->). cbn [fst snd].
pose proof (WfP_cf_set_depot_y3 U 1 1 1 s2 d W2 Hdf) as W3.
pose proof (WfR_of_WfP_cf _ _ _ _ _ W3) as W3r.
destruct (In_split_beg _ _ Hk (wfc_chunks_nodup _ _ _ _ _ W2)) as (l1 & l2 & E & N1 & N2).
apply atok_bind. apply atok_modify. cbn [fst snd st_chunks set_depot]. rewrite E at 1.
rewrite upd_chunk_present by (reflexivity || exact N1). fold (quar_of_cf k).
pose proof (WfR_flip_cf U 1 1 1 (set_depot d s2) l1 k l2 W3r E Hst) as W4.
set (s4 := set_chunks (l1 ++ quar_of_cf k :: l2) (set_depot d s2)) in *.
assert (Hni : ~ In (ck_beg (quar_of_cf k)) (map ck_beg (q_items s4))).
{ cbn [quar_of_cf ck_beg]. replace (q_items s4) with (q_items s2) by reflexivity. intros Hin.
apply in_map_iff in Hin as (k'' & Hb'' & Hk''). pose proof (proj1 (Forall_forall _ _) (wq_items _ (wfc_quarantine _ _ _ _ _ W2)) k'' Hk'') as [H1 H2].
rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply N1 | congruence | apply N2]; rewrite <- Hb''; apply in_map; exact H1. }
assert (CO4 : forall c', chunk_offs s4 c' = chunk_offs s c').
{ intros c'. apply chunk_offs_begs_cf. subst s4. cbn [st_chunks set_chunks]. rewrite <- Fck, E, !map_app. reflexivity. }
assert (CD4 : forall c', cdef s4 c' = cdef s c').
{ intros c'. apply cdef_ext; [reflexivity|]. unfold class_elems. rewrite CO4. reflexivity. }
assert (ROOM4 : rg_mapped_user (reg s4 kBatchClass) + kUserMapSize <= kFreeArrayOffset) by exact Hroom.
apply atok_bind.
(* Quarantine::Put's size test: enqueue up to kQuarantineMax, recycle above it *)
match goal with |- context [if ?c then _ else _] => destruct c eqn:QSZ end; cbv beta iota.
2:{ (* the recycle side: the chunk leaves at once; the drain then runs on an unchanged quarantine *)
eapply atok_mono; [|apply (recycle_chunk_okx_cf U 1 1 1 s4 (quar_of_cf k) true W4 ltac:(subst s4; cbn; apply in_elt) eq_refl Hni)].
intros ns5 [[] s5] ((W5 & (m1 & m2 & EM & EM') & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11) & LEN5). cbn [fst snd] in *.
assert (W5p : WfP_cf U 1 1 1 s5).
{ apply WfP_of_WfR_cf; [exact W5|]. intros c' Hc'.
  assert (E5 : cdef s5 c' = cdef s4 c') by (unfold cdef; rewrite (Q7 c' ltac:(lia)), (Q10 c' Hc'); reflexivity).
  rewrite E5, CD4. exact (wfc_compl0 _ _ _ _ _ W c' Hc'). }
eapply atok_mono; [|apply (md_ok 1 1 1 s5 ns5 W5p)].
intros ns6 [[] s6] (W6 & (G1 & G2 & G3 & G4 & G5) & QT6 & QG6 & UQ6). cbn [snd] in *. unfold free_post_ycf. cbn [snd].
pose proof (wfc_slack _ _ _ _ _ W6).
assert (B5 : blocks s5 = blocks s4).
{ unfold blocks. rewrite EM', EM, !filter_app. cbn [filter is_alloc quar_of_cf ck_state]. reflexivity. }
assert (B4 : blocks s4 = map (fun k => (ck_user k, ck_req k)) (filter is_alloc l1) ++ map (fun k => (ck_user k, ck_req k)) (filter is_alloc l2)).
{ unfold blocks. subst s4. cbn [st_chunks set_chunks]. rewrite filter_app. cbn [filter is_alloc quar_of_cf ck_state]. rewrite map_app. reflexivity. }
assert (B0 : blocks s = map (fun k => (ck_user k, ck_req k)) (filter is_alloc l1) ++ (q, n) :: map (fun k => (ck_user k, ck_req k)) (filter is_alloc l2)).
{ rewrite <- Fbl. unfold blocks. rewrite E, filter_app. cbn [filter]. unfold is_alloc at 2. rewrite Hst, map_app. cbn [map app]. rewrite Hu, Hr. reflexivity. }
assert (UQ0 : unq_cf (set_depot d s2) = unq_cf s) by (apply unq_same_cf; [exact Fck | subst s2 s1; reflexivity | subst s2 s1; reflexivity]).
pose proof (unq_flip_cf (set_depot d s2) l1 k l2 E Hst) as UQ4. fold s4 in UQ4.
pose proof (unq_del_cf s4 s5 m1 (quar_of_cf k) m2 EM EM' eq_refl Q1 Q2) as UQ5. change (ck_n (quar_of_cf k)) with (ck_n k) in UQ5.
splits.
- unfold Wf_cf. eapply WfP_cf_weaken; [exact W6|lia|lia|lia].
- rewrite G1, Q3. subst s4. cbn. exact Fnev.
- eapply secs_ext_trans; [|exact G5]. eapply secs_ext_trans; [|exact Q6]. intros r0 sm0 E0. exists sm0. subst s4. cbn. rewrite ?Fsecs. auto.
- unfold frames. rewrite G2, Q4. subst s4. cbn. rewrite ?Ffs. reflexivity.
- eexists _, _. split; [right; exact B0|]. rewrite G4, B5. exact B4.
- intros (T1 & T2 & T3). split; [exact QT6 | split].
  + rewrite Q2 in QG6. subst s4. cbn [st_qglobal set_chunks set_depot] in QG6. replace (st_qglobal s2) with (st_qglobal s) in QG6 by (subst s2 s1; reflexivity). lia.
  + unfold unq_cf in *. lia. }
eapply atok_mono; [|apply (enqueue_okx_cf U 1 1 1 s4 (quar_of_cf k) true W4 ltac:(lia) ltac:(lia) ltac:(subst s4; cbn; apply in_elt) eq_refl
  ltac:(apply Z.leb_le; exact QSZ) Hni ROOM4)].
intros ns5 [[] s5] ((W5 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & (nb5 & Q5 & NB5) & G5') & DEF5). cbn [fst snd] in *.
assert (W5p : WfP_cf U 0 1 0 s5).
{ apply WfP_of_WfR_cf; [cbn in W5; exact W5|]. intros c' Hc'. rewrite (DEF5 c' Hc'), CD4. exact (wfc_compl0 _ _ _ _ _ W c' Hc'). }
eapply atok_mono; [|apply (md_ok 0 1 0 s5 ns5 W5p)].
intros ns6 [[] s6] (W6 & (G1 & G2 & G3 & G4 & G5) & QT6 & QG6 & UQ6). cbn [snd] in *. unfold free_post_ycf. cbn [snd].
pose proof (wfc_slack _ _ _ _ _ W6).
assert (B4 : blocks s4 = map (fun k => (ck_user k, ck_req k)) (filter is_alloc l1) ++ map (fun k => (ck_user k, ck_req k)) (filter is_alloc l2)).
{ unfold blocks. subst s4. cbn [st_chunks set_chunks]. rewrite filter_app. cbn [filter is_alloc quar_of_cf ck_state]. rewrite map_app. reflexivity. }
assert (B0 : blocks s = map (fun k => (ck_user k, ck_req k)) (filter is_alloc l1) ++ (q, n) :: map (fun k => (ck_user k, ck_req k)) (filter is_alloc l2)).
{ rewrite <- Fbl. unfold blocks. rewrite E, filter_app. cbn [filter]. unfold is_alloc at 2. rewrite Hst, map_app. cbn [map app]. rewrite Hu, Hr. reflexivity. }
assert (UQ0 : unq_cf (set_depot d s2) = unq_cf s) by (apply unq_same_cf; [exact Fck | subst s2 s1; reflexivity | subst s2 s1; reflexivity]).
pose proof (unq_flip_cf (set_depot d s2) l1 k l2 E Hst) as UQ4. fold s4 in UQ4.
pose proof (unq_push_cf s4 s5 (quar_of_cf k) nb5 R1 Q5 G5' NB5) as UQ5. change (ck_n (quar_of_cf k)) with (ck_n k) in UQ5.
splits.
- unfold Wf_cf. eapply WfP_cf_weaken; [exact W6|lia|lia|lia].
- rewrite G1, R7. subst s4. cbn. exact Fnev.
- eapply secs_ext_trans; [|exact G5]. intros r0 sm0 E0. exists sm0. rewrite R2. subst s4. cbn. rewrite ?Fsecs. auto.
- unfold frames. rewrite G2, R5. subst s4. cbn. rewrite ?Ffs. reflexivity.
- eexists _, _. split; [right; exact B0|]. rewrite G4. unfold blocks. rewrite R1. fold (blocks s4). exact B4.
- intros (T1 & T2 & T3). split; [exact QT6 | split].
+ rewrite G5' in QG6. subst s4. cbn [st_qglobal set_chunks set_depot] in QG6. replace (st_qglobal s2) with (st_qglobal s) in QG6 by (subst s2 s1; reflexivity). lia.
+ unfold unq_cf in *. lia.
Qed.

(* The free theorem at the cf request layer. Once YG00cf.v defines free_cf as cgif's free with maybe_drain_cf,
   free_cf p tr s = free_with_cf maybe_drain_cf p tr s by reflexivity, and ml_free_cf is this theorem at
   md := maybe_drain_cf. free never issues KMmapSec, so the atok proof transfers by atok_cf_of_atok. *)
Theorem ml_free_with_cf : forall s p n tr,
Wf_cf U s -> batch_room_cf s -> (p = PNull \/ In (p, n) (blocks s)) -> admits U tr s ->
atok_cf true (free_with_cf md p tr s) (free_post_ycf U s p n).
Proof. intros s p n tr W Hroom Hp Htr. apply atok_cf_of_atok. exact (free_gen_cf s p n tr W Hroom Hp Htr). Qed.
End FREE.
End YG03CF.
