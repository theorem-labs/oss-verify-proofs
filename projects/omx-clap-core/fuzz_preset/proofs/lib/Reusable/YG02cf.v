(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: wfc_fields / wfc_easy carry WfP_cf's new field wfc_qsize. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YG02cf.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), cgif's YG02.v restated over
   the cf invariant WfP_cf (YG01cf.v). cgif's YG02.v is NOT edited: its state-only lemmas (the field
   accessors of set_regions / set_cache / set_nev, prim_user_mapped_set_region, fold_mapped_ge_nth,
   wf_quar_ext, wf_fs_ext, length_init_caches, cache_after_init) are imported and reused as they are.
   What differs from cgif:
   - no regime conjunct: WfP_cf has no wf_regime, so WfP_cf_set_region drops cgif's premise
     `st_nev s <= EV_MAX \/ ...` (YG02.v:180), and a tick needs no side condition;
   - no free-array room: WfP_cf has no wf_fa_room (YG01.v:342-343), so no lemma here carries an fa_room
     premise, and cgif's wf_fa_room_ext (YG02.v:147-152) has no counterpart;
   - wfc_compl0 is a field, so every lemma that changes a class's region or cache takes the class's
     Compl0 equation for the new state as a premise (compl0_keep_cf discharges it when the region keeps
     rg_alloc_user and rg_free);
   - a class may carry the sentinel hole (EXH_HOLE, 0) of YG00cf.v (wfc_holes_exh, cgif's wf_noholes). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* The field tactics, cgif's wf_fields / wf_easy (YG02.v:107-146).                *)
Ltac wfc_fields W :=
pose proof (wfc_len_regions _ _ _ _ _ W) as Xlr; pose proof (wfc_len_cache _ _ _ _ _ W) as Xlc;
pose proof (wfc_reg0 _ _ _ _ _ W) as Xr0; pose proof (wfc_classes _ _ _ _ _ W) as Xcl;
pose proof (wfc_chunks _ _ _ _ _ W) as Xck; pose proof (wfc_chunks_nodup _ _ _ _ _ W) as Xnd;
pose proof (wfc_chunks_ev _ _ _ _ _ W) as Xcev; pose proof (wfc_prim_ev _ _ _ _ _ W) as Xpev;
pose proof (wfc_live _ _ _ _ _ W) as Xlive; pose proof (wfc_quarantine _ _ _ _ _ W) as Xq;
pose proof (wfc_batches_ev _ _ _ _ _ W) as Xbev; pose proof (wfc_secondary _ _ _ _ _ W) as Xsec;
pose proof (wfc_fakestack _ _ _ _ _ W) as Xfs; pose proof (wfc_depot _ _ _ _ _ W) as Xdep;
pose proof (wfc_nev _ _ _ _ _ W) as Xnev; pose proof (wfc_slack _ _ _ _ _ W) as Xsl;
pose proof (wfc_qinited _ _ _ _ _ W) as Xqi; pose proof (wfc_secs_ev _ _ _ _ _ W) as Xsev;
pose proof (wfc_compl0 _ _ _ _ _ W) as Xc0; pose proof (wfc_sec_live _ _ _ _ _ W) as Xsa; pose proof (wfc_qsize _ _ _ _ _ W) as Xqs.

Ltac wfc_easy :=
first [ assumption
| match goal with H : wf_quar ?s0 |- wf_quar _ => apply (wf_quar_ext s0); [reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : Forall (fun k => ck_n k <= kQuarantineMax) (q_items ?s0) |- Forall (fun k => ck_n k <= kQuarantineMax) (q_items _) =>
apply (qsize_ext s0); [reflexivity | reflexivity | exact H] end
| match goal with H : wf_sec_cf ?s0 |- wf_sec_cf _ =>
apply (wf_sec_cf_ext s0); [reflexivity | reflexivity | reflexivity | reflexivity | exact H] end
| match goal with H : wf_fs ?s0 |- wf_fs _ => apply (wf_fs_ext s0); [reflexivity | exact H] end
| match goal with H : all_batches ?s0 <> [] -> st_cache_inited ?s0 = true |- all_batches _ <> [] -> st_cache_inited _ = true =>
first [ exact H | (intros ?HB; apply H; exact HB) ] end
| match goal with |- Z.of_nat (length (st_secs _)) + _ <= st_nev _ =>
solve [ cbn [st_secs st_nev set_chunks set_depot set_regions set_cache set_qthread set_qglobal set_nev set_sec_arr set_sec_reserved
set_cache_inited set_internal_inited set_fs]; lia ] end
| idtac ].

(* ---------------------------------------------------------------------------- *)
(* Region bookkeeping, cgif's regions_nonneg / mapped_le_prim (YG02.v:65-80).     *)
Section YG02CF.
Context {cp : CfParams}.

Lemma regions_nonneg_cf : forall U pp cc bb s j, WfP_cf U pp cc bb s -> (j < length (st_regions s))%nat ->
0 <= rg_mapped_user (nth j (st_regions s) region0).
Proof.
intros U pp cc bb s j W Hj. rewrite (wfc_len_regions _ _ _ _ _ W) in Hj.
destruct j as [|j].
- pose proof (wfc_reg0 _ _ _ _ _ W) as H0. unfold reg, znth in H0. change (Z.to_nat 0) with 0%nat in H0. rewrite H0. cbn. lia.
- pose proof (wrc_alloc _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W (Z.of_nat (S j)) ltac:(lia))) as H.
unfold reg, znth in H. rewrite Nat2Z.id in H. lia.
Qed.

Lemma mapped_le_prim_cf : forall U pp cc bb s c, WfP_cf U pp cc bb s -> 0 <= c <= 31 ->
0 <= rg_mapped_user (reg s c) <= prim_user_mapped s.
Proof.
intros U pp cc bb s c W Hc. unfold reg, znth, prim_user_mapped.
apply fold_mapped_ge_nth; [intros j Hj; eapply regions_nonneg_cf; eassumption|].
rewrite (wfc_len_regions _ _ _ _ _ W). lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* cgif's wf_noholes (YG02.v:118-122). A cf class may carry the sentinel hole.    *)
Lemma wfc_holes_exh : forall U pp cc bb s c, WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
Forall (fun h => h = (EXH_HOLE, 0)) (rg_holes (reg s c)).
Proof. intros U pp cc bb s c W Hc. exact (proj1 (wrc_holes _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W c Hc))). Qed.

End YG02CF.

(* ---------------------------------------------------------------------------- *)
(* Extensionality of the Compl0 field.                                            *)
Lemma compl0_ext_cf : forall s s',
(forall c, 1 <= c <= 31 -> length (class_elems s' c) = length (class_elems s c)) ->
st_regions s' = st_regions s -> Compl0 s -> Compl0 s'.
Proof. intros s s' E R H c Hc. unfold cdef. rewrite E by exact Hc. unfold reg. rewrite R. exact (H c Hc). Qed.

(* ---------------------------------------------------------------------------- *)
(* Class repartition, cgif's cls_ok_repart / cls_ok_take (YG02.v:225-251).         *)
Lemma cls_ok_cf_repart : forall c r p (i : bool) ko bo r' p' (i' : bool) ko' bo' extra,
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

Lemma cls_ok_cf_take : forall c r p i ko bo x rest,
cls_ok_cf c r p i ko bo ->
Permutation (fa_elems (class_size c) (rg_free r) ++ pc_chunks p ++ ko ++ bo) (x :: rest) ->
0 <= x < rg_alloc_user r /\ x mod class_size c = 0 /\ ~ In x rest /\ NoDup rest.
Proof.
intros c r p i ko bo x rest C HP.
pose proof (Permutation_NoDup HP (wrc_nodup _ _ _ _ _ _ C)) as ND. inversion ND; subst.
pose proof (Forall_Permutation _ _ _ HP (wrc_elems _ _ _ _ _ _ C)) as FA. inversion FA; subst. tauto.
Qed.

Section YG02CF2.
Context {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* The tick, cgif's WfP_tick' (YG02.v:153-166). Every st_nev field WfP_cf keeps is *)
(* a LOWER bound, so a tick keeps the invariant with no side condition, and it      *)
(* also grants one unit of each slack: pp, cc and bb enter only lower bounds on    *)
(* st_nev (wfc_prim_ev, wfc_chunks_ev, wfc_secs_ev, wfc_batches_ev).               *)
Lemma WfP_cf_tick : forall U pp cc bb s, WfP_cf U pp cc bb s -> WfP_cf U pp cc bb (set_nev (st_nev s + 1) s).
Proof.
intros U pp cc bb s W. wfc_fields W. constructor; wfc_easy.
- change (Z.of_nat (length (st_chunks s)) + cc <= st_nev s + 1). lia.
- change (prim_user_mapped s + kUserMapSize * pp <= kUserMapSize * (st_nev s + 1)). unfold kUserMapSize in *. lia.
- change (Z.of_nat (length (all_batches s)) + bb <= st_nev s + 1). lia.
- change (0 <= st_nev s + 1). lia.
Qed.

Lemma WfP_cf_tick_credit : forall U pp cc bb s,
WfP_cf U pp cc bb s -> WfP_cf U (pp + 1) (cc + 1) (bb + 1) (set_nev (st_nev s + 1) s).
Proof.
intros U pp cc bb s W. wfc_fields W. constructor; wfc_easy.
- change (Z.of_nat (length (st_chunks s)) + (cc + 1) <= st_nev s + 1). lia.
- change (prim_user_mapped s + kUserMapSize * (pp + 1) <= kUserMapSize * (st_nev s + 1)). unfold kUserMapSize in *. lia.
- change (Z.of_nat (length (all_batches s)) + (bb + 1) <= st_nev s + 1). lia.
- change (0 <= st_nev s + 1). lia.
- lia.
Qed.

(* cgif's own shape (YG02.v:153-155), with neither of its side conditions. *)
Lemma WfP_cf_tick' : forall U s, Wf_cf U s -> WfP_cf U 1 1 1 (set_nev (st_nev s + 1) s).
Proof. intros U s W. exact (WfP_cf_tick_credit U 0 0 0 s W). Qed.

(* ---------------------------------------------------------------------------- *)
(* The Compl0 premise of the region / cache updates, when the class keeps its      *)
(* carved bytes and its free list.                                                 *)
Lemma compl0_keep_cf : forall U pp cc bb s c r', WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
rg_alloc_user r' = rg_alloc_user (reg s c) -> rg_free r' = rg_free (reg s c) ->
rg_alloc_user r' - class_size c * Z.of_nat (length (fa_elems (class_size c) (rg_free r') ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c)) = 0.
Proof. intros U pp cc bb s c r' W Hc EA EF. rewrite EA, EF. exact (wfc_compl0 _ _ _ _ _ W c Hc). Qed.

(* ---------------------------------------------------------------------------- *)
(* cgif's WfP_set_region (YG02.v:173-204) without the free-array room (:178-179)   *)
(* and the regime premise (:180), plus the class's Compl0 equation.                *)
Lemma WfP_cf_set_region : forall U pp cc bb s c r' pp',
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
cls_ok_cf c r' (cache s c) (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
0 <= pp' ->
prim_user_mapped s - rg_mapped_user (reg s c) + rg_mapped_user r' + kUserMapSize * pp' <= kUserMapSize * st_nev s ->
rg_alloc_user r' - class_size c * Z.of_nat (length (fa_elems (class_size c) (rg_free r') ++ pc_chunks (cache s c) ++ chunk_offs s c ++ batch_offs s c)) = 0 ->
WfP_cf U pp' cc bb (set_regions (zupd c r' (st_regions s)) s).
Proof.
intros U pp cc bb s c r' pp' W Hc Hcls Hpp' Hbound Hc0.
assert (Hlen : (Z.to_nat c < length (st_regions s))%nat) by (rewrite (wfc_len_regions _ _ _ _ _ W); lia).
wfc_fields W. constructor; wfc_easy.
- cbn. rewrite zupd_length. assumption.
- rewrite reg_upd_other; [assumption | lia | lia | lia].
- intros c' Hc'. unfold wf_class_cf. rewrite cache_set_regions, chunk_offs_set_regions, batch_offs_set_regions. cbn [st_cache_inited set_regions].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite reg_upd_same; [exact Hcls | lia | exact Hlen].
+ rewrite reg_upd_other; [ | lia | lia | exact Hne]. exact (Xcl c' Hc').
- change (prim_user_mapped (set_regions (zupd c r' (st_regions s)) s) + kUserMapSize * pp' <= kUserMapSize * st_nev s).
rewrite prim_user_mapped_set_region; [| lia | exact Hlen]. exact Hbound.
- lia.
- intros c' Hc'. unfold cdef, class_elems. rewrite cache_set_regions, chunk_offs_set_regions, batch_offs_set_regions.
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite reg_upd_same; [exact Hc0 | lia | exact Hlen].
+ rewrite reg_upd_other; [ | lia | lia | exact Hne]. exact (Xc0 c' Hc').
Qed.

(* ---------------------------------------------------------------------------- *)
(* cgif's WfP_set_pc (YG02.v:205-224) without the free-array room (:208-209),      *)
(* plus the class's Compl0 equation.                                               *)
Lemma WfP_cf_set_pc : forall U pp cc bb s c p',
WfP_cf U pp cc bb s -> 1 <= c <= 31 ->
cls_ok_cf c (reg s c) p' (st_cache_inited s) (chunk_offs s c) (batch_offs s c) ->
rg_alloc_user (reg s c) - class_size c * Z.of_nat (length (fa_elems (class_size c) (rg_free (reg s c)) ++ pc_chunks p' ++ chunk_offs s c ++ batch_offs s c)) = 0 ->
WfP_cf U pp cc bb (set_cache (zupd c p' (st_cache s)) s).
Proof.
intros U pp cc bb s c p' W Hc Hcls Hc0.
assert (Hlen : (Z.to_nat c < length (st_cache s))%nat) by (rewrite (wfc_len_cache _ _ _ _ _ W); lia).
wfc_fields W. constructor; wfc_easy.
- cbn. rewrite zupd_length. assumption.
- intros c' Hc'. unfold wf_class_cf. rewrite reg_set_cache, chunk_offs_set_cache, batch_offs_set_cache. cbn [st_cache_inited set_cache].
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite cache_upd_same; [exact Hcls | lia | exact Hlen].
+ rewrite cache_upd_other; [ | lia | lia | exact Hne]. exact (Xcl c' Hc').
- intros c' Hc'. unfold cdef, class_elems. rewrite reg_set_cache, chunk_offs_set_cache, batch_offs_set_cache.
destruct (Z.eq_dec c c') as [<-|Hne].
+ rewrite cache_upd_same; [exact Hc0 | lia | exact Hlen].
+ rewrite cache_upd_other; [ | lia | lia | exact Hne]. exact (Xc0 c' Hc').
Qed.

(* ---------------------------------------------------------------------------- *)
(* cgif's WfP_init_caches (YG02.v:272-293). init_caches keeps every pc_chunks, so  *)
(* class_elems and with it Compl0 are unchanged.                                   *)
Lemma WfP_cf_init_caches : forall U pp cc bb s,
WfP_cf U pp cc bb s -> st_cache_inited s = false ->
WfP_cf U pp cc bb (set_cache_inited true (set_cache (init_caches (st_cache s)) s)).
Proof.
intros U pp cc bb s W Hi. wfc_fields W. constructor; wfc_easy.
- cbn [st_cache set_cache_inited set_cache]. apply length_init_caches.
- intros c' Hc'. pose proof (Xcl c' Hc') as C. unfold wf_class_cf in *.
rewrite reg_set_cache_inited, reg_set_cache, chunk_offs_set_cache_inited, chunk_offs_set_cache,
batch_offs_set_cache_inited, batch_offs_set_cache, cache_after_init by lia.
cbn [st_cache_inited set_cache_inited]. rewrite Hi in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as Hp. cbn in Hp. rewrite Hp in C |- *. cbn [pc_chunks pclass0].
eapply (cls_ok_cf_repart c' _ _ false _ _ _ _ true _ _ []); try exact C; try reflexivity.
+ exact (wrc_runs _ _ _ _ _ _ C).
+ exact (wrc_fa_len _ _ _ _ _ _ C).
+ cbn [pc_max pc_chunks length Z.of_nat]. split; [reflexivity|]. pose proof (class_ok c' Hc'). lia.
- intros _. reflexivity.
- intros c' Hc'. pose proof (Xc0 c' Hc') as R. unfold cdef, class_elems in *.
rewrite reg_set_cache_inited, reg_set_cache, chunk_offs_set_cache_inited, chunk_offs_set_cache,
batch_offs_set_cache_inited, batch_offs_set_cache, cache_after_init by lia.
cbn [pc_chunks]. exact R.
Qed.

End YG02CF2.
