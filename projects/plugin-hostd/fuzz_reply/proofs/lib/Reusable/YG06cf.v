(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YG06cf.v, sha256 94589f91038b31709b4bfc37a11c6dcb1c25fe7a4ff9994ae62ad8be1053e5b9.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.
   Plus the P'' (Univ trace carrier) delta of commit 94ab015e127b for cgif/cgif_file_fuzzer/lib/YG06cf.v, taken 3-way (base d94d29d53c8). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the class-geometry steps and
   the map atok lemmas of cgif's YG06.v restated over WfP_cf (YG01cf.v) and YG00cf.v's map_more_user_cf.
   cgif's YG06.v is NOT edited: its state-only helpers (upd_reg, upd_pc, atok_set_region, round_up_step,
   NoDup_filter, NoDup_del_hole, the cbnr / splits tactics) are imported and reused.
   What differs from cgif:
   - the holes: a class may carry the sentinel (EXH_HOLE, 0); exh_holes_* replace hole_ok_del, and
     exh_holes_disjoint discharges areq_ok's hole conditions (YG01.v:19, :23-24) for it;
   - cls_ok_cf_map_user's bound is `rg_mapped_user r + kUserMapSize <= kFreeArrayOffset`, the test that
     map_more_user_cf makes before it maps (YG00cf.v:150), taken as a HYPOTHESIS, never `kUserMapSize * EV_MAX`;
   - map_more_user_cf's class-full arm is a refusal that returns false (YG00cf.v:160); its tail
     `set_exh_cf c ;; ret false` is set_exh_ret_cf_ok, and map_more_user_cf_full_tok reduces the arm to
     `errb_report_cf c ;; set_exh_cf c ;; ret false` in the cf request layer (YGcfTok.v), the only layer in
     which errb_map_cf's KMmapSec is admissible. The errb_report_cf step itself is not proved here (it
     belongs to the errbuf owner), so map_more_user_cf_ok takes the premise
     `rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset \/ exh_mem_cf s c = true`, under which
     errb_report_cf asks nothing. Every atok lemma here also has its atok_cf form (suffix _tok).
   - no free-array room: WfP_cf has no wf_fa_room (YG01.v:449-450), so cgif's fa_room_populate
     (YG06.v:67-83) and fa_room_keep (:84-85) have no counterpart, and no lemma here carries an fa_room
     premise. The free array grows when it must: ensure_free_array_ok_cf is the growth step. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YG02cf YGcfTok.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* The sentinel hole, in place of cgif's hole_ok_del (YG06.v:86-87).               *)
Lemma exh_holes_del : forall off l, Forall (fun h => h = (EXH_HOLE, 0)) l -> Forall (fun h => h = (EXH_HOLE, 0)) (del_hole off l).
Proof.
intros off l H. unfold del_hole. apply Forall_forall. intros h Hh. apply filter_In in Hh as [Hh _].
exact (proj1 (Forall_forall _ _) H h Hh).
Qed.

Lemma exh_holes_add : forall l, Forall (fun h => h = (EXH_HOLE, 0)) l -> Forall (fun h => h = (EXH_HOLE, 0)) (add_hole (EXH_HOLE, 0) l).
Proof.
intros l H. unfold add_hole. constructor; [reflexivity|]. apply Forall_forall. intros h Hh. apply filter_In in Hh as [Hh _].
exact (proj1 (Forall_forall _ _) H h Hh).
Qed.

Lemma NoDup_add_hole : forall h l, NoDup l -> NoDup (add_hole h l).
Proof.
intros h l H. unfold add_hole. constructor.
- intros Hin. apply filter_In in Hin as [_ Hf]. rewrite Z.eqb_refl in Hf. cbn in Hf. discriminate Hf.
- apply NoDup_filter. exact H.
Qed.

(* The sentinel meets areq_ok's hole conditions for every map at a nonnegative     *)
(* offset: fst h + snd h = -1 <= off.                                              *)
Lemma exh_holes_disjoint : forall l off len, 0 <= off -> Forall (fun h => h = (EXH_HOLE, 0)) l ->
Forall (fun h => fst h = off /\ snd h = len \/ fst h + snd h <= off \/ off + len <= fst h) l.
Proof.
intros l off len Hoff H. eapply Forall_impl; [|exact H]. intros h ->. right. left. cbn [fst snd]. unfold EXH_HOLE. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* Class geometry, cgif's cls_ok_map_user / cls_ok_map_fa (YG06.v:95-125).         *)
Lemma cls_ok_cf_set_holes : forall c r p i ko bo hs,
cls_ok_cf c r p i ko bo -> Forall (fun h => h = (EXH_HOLE, 0)) hs -> NoDup hs ->
cls_ok_cf c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r) hs) p i ko bo.
Proof. intros c r p i ko bo hs C H1 H2. destruct C. constructor; cbnr; try assumption. split; assumption. Qed.

Lemma cls_ok_cf_map_user : forall c r p i ko bo,
cls_ok_cf c r p i ko bo -> rg_mapped_user r - rg_alloc_user r < kMaxSize ->
rg_mapped_user r + kUserMapSize <= kFreeArrayOffset ->
cls_ok_cf c (mkRegion (rg_mapped_user r + kUserMapSize) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(del_hole (rg_mapped_user r) (rg_holes r))) p i ko bo.
Proof.
intros c r p i ko bo C Hcv Hroom.
pose proof (wrc_alloc _ _ _ _ _ _ C) as A. pose proof (wrc_mapped_al _ _ _ _ _ _ C) as Mal.
pose proof (wrc_fa _ _ _ _ _ _ C) as F. pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh Hnd].
constructor; cbnr; try (exact (wrc_alloc_al _ _ _ _ _ _ C)); try (exact (wrc_fa_len _ _ _ _ _ _ C)); try (exact (wrc_fa_bound _ _ _ _ _ _ C));
try (exact (wrc_runs _ _ _ _ _ _ C)); try (exact (wrc_nodup _ _ _ _ _ _ C)); try (exact (wrc_elems _ _ _ _ _ _ C)); try (exact (wrc_cache _ _ _ _ _ _ C)).
- unfold kUserMapSize in *. lia.
- unfold kUserMapSize, kMaxSize in *. lia.
- rewrite Z.add_mod, Z.mod_same by (unfold kUserMapSize; lia). rewrite Mal. reflexivity.
- exact F.
- split; [|apply NoDup_del_hole; exact Hnd]. apply exh_holes_del. exact Hh.
- exact Hroom.
Qed.

Lemma cls_ok_cf_map_fa : forall c r p i ko bo fa',
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
split; [|apply NoDup_del_hole; exact Hnd]. apply exh_holes_del. exact Hh.
Qed.

(* The one map step of user memory: a request of at most kMaxSize bytes past the  *)
(* carved end rounds up to exactly one kUserMapSize.                               *)
Lemma round_up_user_step : forall x, 0 < x <= kUserMapSize -> round_up x kUserMapSize = kUserMapSize.
Proof.
intros x Hx. rewrite <- (Z.add_0_l kUserMapSize) at 2.
apply round_up_step; [unfold kUserMapSize; lia | reflexivity | lia].
Qed.

Section YG06CF.
Context {cp : CfParams}.

Lemma WfP_cf_len_regions : forall U pp cc bb s c, WfP_cf U pp cc bb s -> 0 <= c <= 31 -> (Z.to_nat c < length (st_regions s))%nat.
Proof. intros U pp cc bb s c W Hc. rewrite (wfc_len_regions _ _ _ _ _ W). lia. Qed.
Lemma WfP_cf_len_cache : forall U pp cc bb s c, WfP_cf U pp cc bb s -> 0 <= c <= 31 -> (Z.to_nat c < length (st_cache s))%nat.
Proof. intros U pp cc bb s c W Hc. rewrite (wfc_len_cache _ _ _ _ _ W). lia. Qed.

(* ---------------------------------------------------------------------------- *)
(* cgif's WfP_set_region_pc (YG06.v:487-524): both updates of one class at once,  *)
(* without the free-array room (:492-493) and the regime premise (:494), plus the *)
(* class's Compl0 equation. With wfc_compl0 a field, this is the form a step that  *)
(* moves records between the free list and the cache needs: the state between the *)
(* two updates breaks Compl0.                                                      *)
Lemma WfP_cf_set_region_pc : forall U pp cc bb s c r' p' pp',
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
cls_ok_cf c r' p' (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
0 <= pp' ->
prim_user_mapped s - rg_mapped_user (reg s c) + rg_mapped_user r' + kUserMapSize * pp' <= kUserMapSize * st_nev s ->
rg_alloc_user r' - class_size c * Z.of_nat (length (fa_elems (class_size c) (rg_free r') ++ pc_chunks p' ++ chunk_offs s c ++ batch_offs s c)) = 0 ->
WfP_cf U pp' cc bb (upd_pc c p' (upd_reg c r' s)).
Proof.
intros U pp cc bb s c r' p' pp' W Hc Hcls Hpp' Hbound Hc0.
assert (Hlen : (Z.to_nat c < length (st_regions s))%nat) by (rewrite (wfc_len_regions _ _ _ _ _ W); lia).
assert (Hlen' : (Z.to_nat c < length (st_cache s))%nat) by (rewrite (wfc_len_cache _ _ _ _ _ W); lia).
wfc_fields W. unfold upd_pc, upd_reg. constructor; wfc_easy.
- cbn [st_regions set_cache set_regions]. rewrite zupd_length. assumption.
- cbn [st_cache st_regions set_cache set_regions]. rewrite zupd_length. assumption.
- unfold reg in *. cbn [st_regions set_cache set_regions]. rewrite znth_zupd_other; [assumption | lia | lia | lia].
- intros c' Hc'. unfold wf_class_cf in *. unfold reg, cache in *. cbn [st_regions st_cache st_cache_inited set_cache set_regions].
change (chunk_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (chunk_offs s c').
change (batch_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (batch_offs s c').
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite !znth_zupd_same by first [lia | assumption]. exact Hcls.
+ rewrite !znth_zupd_other by first [lia | assumption]. exact (Xcl c' Hc').
- change (prim_user_mapped (set_regions (zupd c r' (st_regions s)) s) + kUserMapSize * pp' <= kUserMapSize * st_nev s).
rewrite prim_user_mapped_set_region; [| lia | exact Hlen]. exact Hbound.
- lia.
- intros c' Hc'. unfold cdef, class_elems, reg, cache in *. cbn [st_regions st_cache set_cache set_regions].
change (chunk_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (chunk_offs s c').
change (batch_offs (set_cache (zupd c p' (st_cache s)) (set_regions (zupd c r' (st_regions s)) s)) c') with (batch_offs s c').
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite !znth_zupd_same by first [lia | assumption]. exact Hc0.
+ rewrite !znth_zupd_other by first [lia | assumption]. exact (Xc0 c' Hc').
Qed.

(* ---------------------------------------------------------------------------- *)
(* ensure_free_array (cgif's function, which populate_cf calls), cgif's           *)
(* ensure_free_array_ok (YG06.v:145-195) without the regime conjunct.              *)
Definition ensure_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (c need : Z) (sof : bool) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfP_cf U pp cc bb s' /\
rg_mapped_user r' = rg_mapped_user (reg s c) /\ rg_alloc_user r' = rg_alloc_user (reg s c) /\
rg_free r' = rg_free (reg s c) /\ rg_mapped_fa (reg s c) <= rg_mapped_fa r' /\
(ok = true -> 4 * need <= rg_mapped_fa r') /\ (ok = false -> ns = false /\ sof = false).

Lemma ensure_free_array_ok_cf : forall U pp cc bb s c need sof ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
fa_len (rg_free (reg s c)) <= need ->
4 * need <= rg_mapped_fa (reg s c) + kFreeArrayMapSize ->
4 * need <= kFreeArrayMax ->
atok ns (ensure_free_array c need sof s) (ensure_post_cf U pp cc bb s c need sof).
Proof.
intros U pp cc bb s c need sof ns W Hc Hlen Hneed Hneed2.
pose proof (wfc_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_fa _ _ _ _ _ _ C) as [F0 Fal]. pose proof (wrc_fa_bound _ _ _ _ _ _ C) as Fb.
pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh Hnd]. pose proof (wfc_slack _ _ _ _ _ W) as SL.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_cf_len_regions; [exact W | lia]).
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
apply exh_holes_disjoint; [unfold kFreeArrayOffset; lia | exact Hh]. }
intros z Hz. cbn [fst snd progz]. destruct (aGranted z) eqn:Eg.
+ apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. split; [reflexivity|]. rewrite RU.
split; [| cbnr; splits; try reflexivity; try lia; intros; discriminate].
eapply WfP_cf_set_region; [exact W | exact Hc | | lia | pose proof (wfc_prim_ev _ _ _ _ _ W); cbnr; lia
| apply (compl0_keep_cf U pp cc bb s c _ W Hc); reflexivity].
apply cls_ok_cf_map_fa; [exact C | lia | | ].
* rewrite Z.add_mod, Fal, Z.mod_same by (unfold kFreeArrayMapSize; lia). reflexivity.
* exact B29.
+ apply atok_bind. replace (aDestroyed z) with false by (unfold aDestroyed; destruct Hz as [-> | ->]; reflexivity).
apply atok_ret. cbn [fst snd]. unfold aGranted in Eg. rewrite Eg.
destruct sof; [apply atok_spin|]. apply atok_ret. exists (reg s c). rewrite ES. splits; auto; try lia.
Qed.

(* The same step in the cf request layer (YGcfTok.v), which the malloc / free laws use. *)
Lemma ensure_free_array_ok_cf_tok : forall U pp cc bb s c need sof ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
fa_len (rg_free (reg s c)) <= need ->
4 * need <= rg_mapped_fa (reg s c) + kFreeArrayMapSize ->
4 * need <= kFreeArrayMax ->
atok_cf ns (ensure_free_array c need sof s) (ensure_post_cf U pp cc bb s c need sof).
Proof.
intros U pp cc bb s c need sof ns W Hc H1 H2 H3. apply atok_cf_of_atok.
exact (ensure_free_array_ok_cf U pp cc bb s c need sof ns W Hc H1 H2 H3).
Qed.

(* ---------------------------------------------------------------------------- *)
(* The tail of the refusal arm (YG00cf.v:160): flag the class, return false.       *)
Definition exh_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (c : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
ok = false /\ exists r', s' = upd_reg c r' s /\ WfP_cf U pp cc bb s' /\
rg_mapped_user r' = rg_mapped_user (reg s c) /\ rg_alloc_user r' = rg_alloc_user (reg s c) /\
rg_free r' = rg_free (reg s c) /\ rg_mapped_fa r' = rg_mapped_fa (reg s c) /\
existsb (fun h => fst h =? EXH_HOLE) (rg_holes r') = true.

Lemma set_exh_ret_cf_ok : forall U pp cc bb s c ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
atok ns ((set_exh_cf c ;; ret false) s) (exh_post_cf U pp cc bb s c).
Proof.
intros U pp cc bb s c ns W Hc.
pose proof (wfc_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh Hnd]. pose proof (wfc_slack _ _ _ _ _ W) as SL.
apply atok_bind. unfold set_exh_cf. apply atok_bind. apply atok_get_region. cbn [fst snd].
apply atok_set_region. cbn [fst snd]. apply atok_ret.
split; [reflexivity|]. eexists. split; [reflexivity|].
split; [| cbnr; splits; try reflexivity; apply add_hole_exh].
eapply WfP_cf_set_region; [exact W | exact Hc | | lia | | apply (compl0_keep_cf U pp cc bb s c _ W Hc); reflexivity].
- apply cls_ok_cf_set_holes; [exact C | apply exh_holes_add; exact Hh | apply NoDup_add_hole; exact Hnd].
- pose proof (wfc_prim_ev _ _ _ _ _ W). cbnr. lia.
Qed.

Lemma set_exh_ret_cf_tok : forall U pp cc bb s c ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
atok_cf ns ((set_exh_cf c ;; ret false) s) (exh_post_cf U pp cc bb s c).
Proof. intros U pp cc bb s c ns W Hc. apply atok_cf_of_atok. exact (set_exh_ret_cf_ok U pp cc bb s c ns W Hc). Qed.

Section MAP.
Context {ci : CfImg}.

(* ---------------------------------------------------------------------------- *)
(* map_more_user_cf, cgif's map_post / map_more_user_ok (YG06.v:270-308).          *)
(* ok = false now has two causes: the kernel refused the map (ns = false, as in    *)
(* cgif), or the class is full and the arm refused (the class's byte is set).      *)
Definition map_post_cf (U : Univ) (pp cc bb : Z) (s : astate) (c need : Z) (ns : bool) (res : bool * astate) : Prop :=
let (ok, s') := res in
exists r', s' = upd_reg c r' s /\ WfP_cf U (pp - 1) cc bb s' /\
rg_alloc_user r' = rg_alloc_user (reg s c) /\ rg_free r' = rg_free (reg s c) /\ rg_mapped_fa r' = rg_mapped_fa (reg s c) /\
rg_mapped_user (reg s c) <= rg_mapped_user r' <= rg_mapped_user (reg s c) + kUserMapSize /\
(ok = true -> rg_alloc_user (reg s c) + need * class_size c <= rg_mapped_user r') /\
(ok = false -> ns = false \/
(kFreeArrayOffset < rg_mapped_user (reg s c) + kUserMapSize /\ existsb (fun h => fst h =? EXH_HOLE) (rg_holes r') = true)).

(* The class-full arm IS the refusal: for a class other than kBatchClass whose next *)
(* map does not fit under kFreeArrayOffset, map_more_user_cf runs exactly           *)
(* `errb_report_cf c ;; set_exh_cf c ;; ret false`. No mcheck is involved. Stated   *)
(* in the cf request layer, since the errbuf's KMmapSec is admissible only there.   *)
Lemma map_more_user_cf_full_tok : forall U pp cc bb s c need ns (Q : bool -> bool * astate -> Prop),
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> c <> kBatchClass ->
0 < need * class_size c <= kMaxSize ->
rg_mapped_user (reg s c) < rg_alloc_user (reg s c) + need * class_size c ->
kFreeArrayOffset < rg_mapped_user (reg s c) + kUserMapSize ->
atok_cf ns ((errb_report_cf c ;; set_exh_cf c ;; ret false) s) Q ->
atok_cf ns (map_more_user_cf c need s) Q.
Proof.
intros U pp cc bb s c need ns Q W Hc N24 Hneed Hlt Hover H.
pose proof (wrc_alloc _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c Hc)) as A.
unfold map_more_user_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; [contradiction|]. cbv beta iota.
apply atok_cf_bind. apply atok_cf_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c) + need * class_size c)) as [_|Hge]; [|lia].
rewrite (round_up_user_step (rg_alloc_user (reg s c) + need * class_size c - rg_mapped_user (reg s c)))
by (unfold kUserMapSize, kMaxSize in *; lia).
destruct (Z.leb_spec (rg_mapped_user (reg s c) + kUserMapSize) kFreeArrayOffset) as [Hf|_]; [lia|].
exact H.
Qed.

Lemma map_more_user_cf_ok : forall U pp cc bb s c need ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp ->
0 < need * class_size c <= kMaxSize ->
(* class kBatchClass keeps cgif's text, whose mcheck (YG00.v:285) needs the map to fit *)
(c = kBatchClass -> rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset) ->
(* until errb_report_cf has its atok form: either the map fits, or the class's byte is
   already set, so errb_report_cf asks nothing *)
(rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset \/ exh_mem_cf s c = true) ->
atok ns (map_more_user_cf c need s) (map_post_cf U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hneed H24 Hfull.
pose proof (wfc_classes _ _ _ _ _ W c Hc) as C. unfold wf_class_cf in C.
pose proof (wrc_alloc _ _ _ _ _ _ C) as A. pose proof (wrc_mapped_al _ _ _ _ _ _ C) as Mal.
pose proof (wrc_holes _ _ _ _ _ _ C) as [Hh Hnd]. pose proof (wfc_slack _ _ _ _ _ W) as SL.
assert (HL : (Z.to_nat c < length (st_regions s))%nat) by (eapply WfP_cf_len_regions; [exact W | lia]).
assert (ES : upd_reg c (reg s c) s = s) by (apply upd_reg_same; [lia | exact HL]).
assert (Wk : WfP_cf U (pp - 1) cc bb s) by (eapply WfP_cf_weaken; [exact W | lia | lia | lia]).
(* The map request and its two outcomes, shared by both arms. *)
assert (ASK : rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset ->
rg_mapped_user (reg s c) < rg_alloc_user (reg s c) + need * class_size c ->
atok ns ((z <- askz (KMapUser c (rg_mapped_user (reg s c)) kUserMapSize) ;;
if aGranted z then
(set_region c (mkRegion (rg_mapped_user (reg s c) + kUserMapSize) (rg_alloc_user (reg s c)) (rg_mapped_fa (reg s c))
(rg_free (reg s c)) (del_hole (rg_mapped_user (reg s c)) (rg_holes (reg s c)))) ;; ret true)
else
((if aDestroyed z
then set_region c (mkRegion (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c)) (rg_mapped_fa (reg s c)) (rg_free (reg s c))
(add_hole (rg_mapped_user (reg s c), kUserMapSize) (rg_holes (reg s c))))
else ret tt) ;; ret false)) s)
(map_post_cf U pp cc bb s c need)).
{ intros Hfit Hlt. apply atok_bind. apply atok_askz.
{ cbn [areq_ok]. splits; try reflexivity; try lia; try exact Mal; try (unfold kFreeArrayOffset, kUserMapSize in *; lia).
apply exh_holes_disjoint; [lia | exact Hh]. }
intros z Hz. cbn [fst snd progz]. unfold aGranted. destruct (Z.eqb_spec z 1) as [->|Hz1].
- apply atok_bind. apply atok_set_region. cbn [fst snd]. apply atok_ret.
eexists. split; [reflexivity|]. split.
+ eapply WfP_cf_set_region; [exact W | exact Hc | apply cls_ok_cf_map_user; [exact C | unfold kMaxSize in *; lia | exact Hfit] | lia
| pose proof (wfc_prim_ev _ _ _ _ _ W); cbnr; unfold kUserMapSize in *; lia
| apply (compl0_keep_cf U pp cc bb s c _ W Hc); reflexivity].
+ cbnr. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [unfold kUserMapSize; lia|].
split; [intros _; unfold kUserMapSize, kMaxSize in *; lia | intros E; discriminate E].
- apply atok_bind. replace (aDestroyed z) with false by (unfold aDestroyed; destruct Hz as [-> | ->]; [reflexivity | exfalso; apply Hz1; reflexivity]).
apply atok_ret. cbn [fst snd]. apply atok_ret. exists (reg s c). rewrite ES.
split; [reflexivity|]. split; [exact Wk|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [unfold kUserMapSize; lia|]. split; [intros E; discriminate E | intros _; left; reflexivity]. }
(* No map needed: the carved end already covers the request. *)
assert (NOMAP : rg_alloc_user (reg s c) + need * class_size c <= rg_mapped_user (reg s c) ->
map_post_cf U pp cc bb s c need ns (true, s)).
{ intros Hge. exists (reg s c). rewrite ES.
split; [reflexivity|]. split; [exact Wk|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [unfold kUserMapSize; lia|]. split; [intros _; exact Hge | intros E; discriminate E]. }
unfold map_more_user_cf. destruct (Z.eqb_spec c kBatchClass) as [E24|N24]; cbv beta iota.
- (* class kBatchClass: cgif's map_more_user, its mcheck discharged by H24 *)
specialize (H24 E24). unfold map_more_user. apply atok_bind. apply atok_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c) + need * class_size c)) as [Hlt|Hge].
+ rewrite (round_up_user_step (rg_alloc_user (reg s c) + need * class_size c - rg_mapped_user (reg s c)))
by (unfold kUserMapSize, kMaxSize in *; lia).
apply atok_bind. apply atok_mcheck; [apply Z.leb_le; exact H24|]. cbn [fst snd]. exact (ASK H24 Hlt).
+ apply atok_ret. exact (NOMAP Hge).
- (* the cf arm *)
apply atok_bind. apply atok_get_region. cbn [fst snd].
destruct (Z.ltb_spec (rg_mapped_user (reg s c)) (rg_alloc_user (reg s c) + need * class_size c)) as [Hlt|Hge].
+ rewrite (round_up_user_step (rg_alloc_user (reg s c) + need * class_size c - rg_mapped_user (reg s c)))
by (unfold kUserMapSize, kMaxSize in *; lia).
destruct (Z.leb_spec (rg_mapped_user (reg s c) + kUserMapSize) kFreeArrayOffset) as [Hfit|Hover].
* exact (ASK Hfit Hlt).
* (* the class-full refusal; under the interim premise the byte is already set *)
destruct Hfull as [Hf|Hx]; [lia|].
apply atok_bind. unfold errb_report_cf. apply atok_bind. apply atok_get. cbn [fst snd]. rewrite Hx.
apply atok_ret. cbn [fst snd].
eapply atok_mono; [|exact (set_exh_ret_cf_ok U (pp - 1) cc bb s c ns Wk Hc)].
intros b [ok s'] (Eok & r' & -> & W' & E1 & E2 & E3 & E4 & EX). subst ok.
exists r'. split; [reflexivity|]. split; [exact W'|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
split; [rewrite E1; unfold kUserMapSize; lia|]. split; [intros E; discriminate E | intros _; right; split; [lia | exact EX]].
+ apply atok_ret. exact (NOMAP Hge).
Qed.

Lemma map_more_user_cf_ok_tok : forall U pp cc bb s c need ns,
WfP_cf U pp cc bb s -> 1 <= c <= 31 -> 1 <= pp ->
0 < need * class_size c <= kMaxSize ->
(c = kBatchClass -> rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset) ->
(rg_mapped_user (reg s c) + kUserMapSize <= kFreeArrayOffset \/ exh_mem_cf s c = true) ->
atok_cf ns (map_more_user_cf c need s) (map_post_cf U pp cc bb s c need).
Proof.
intros U pp cc bb s c need ns W Hc Hpp Hneed H24 Hfull. apply atok_cf_of_atok.
exact (map_more_user_cf_ok U pp cc bb s c need ns W Hc Hpp Hneed H24 Hfull).
Qed.

End MAP.
End YG06CF.
