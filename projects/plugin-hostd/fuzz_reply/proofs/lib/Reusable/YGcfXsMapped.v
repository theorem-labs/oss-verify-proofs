(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfXsMapped.v, sha256 9cba783ceb7348eaa3258bf254bdaf8a2aa307a231dce3dbf964bbc21aeb7f1b (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: km_fr_free_cf's script covers free_cf's recycle side (km_fr_recycle_chunk); statements unchanged. A change request to a Theorem Labs lane *)
(* Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the text is otherwise unchanged. *)
(* Theorem Labs, 2026-10: the keep lemmas of xs_mapped_cf (YGcfXs.v), the walk fact that the error-message-buffer
   extent xs_cf ly S is one of the LPS model's maps. xs_fresh_of_grant (YGcfXs.v) reads it at a secondary grant, so a
   walk invariant that carries it must keep it across every step that changes vm_maps or xs_cf.
   - Section 1, the map frame mkeep D md md': every map of md whose base is not the base of an extent in D stays a
     map of md'. Each LPS model operation the allocator walks use is one: with_vm_backing, same_but_materialized,
     mmap_model, grant_md, fixedin_ok_model keep every map (D = []); munmap_model (w64 c) drops only the maps based
     at c (D = [(c, _)]).
   - Section 2, the generic keep (xs_mapped_cf_frame) and the base-apartness facts that feed it: an xs extent is
     apart from every sec extent (xs_sec_apart, from xs_placed_cf's zdisjoint), from the shadow band
     (xs_shadow_apart, from in_app), and from a fresh grant (errb_fresh_apart, from region_free).
   - Section 3, one lemma per step: map growth (KMapUser / KMapFreeArray / KMapPtrArray, populate_cf / map_more_user /
     ensure_free_array), the secondary grant (sec_alloc's KMmapSec, and the whole sec_md chain of c-asan's AIfaceS
     post), the shadow remap (KShadowRemap), the secondary unmap (sec_dealloc's KMunmapSec), the class-full errbuf
     map / remap (errb_map_cf, with the munmap of the old buffer).
   - Section 4, the compositions over free_cf / malloc_cf / realloc_tree_with, in the apath form of
     free_leaf_cf_xs_keep_path: all-paths model facts (cfx_ipost / cfxm_kpost, as YGcfXs.v section 4b), then the
     keep with the walk's map frame as the premise.
   No address, no unit numeral. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK13 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG08cf YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK0v YA05 YA09 YG0b YG04 ReallocP YGcfAmx.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section XM. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The map frame of an LPS step.                                               *)
Definition mkeep (D : list (Z * Z)) (md md' : Model) : Prop :=
forall q, In q (vm_maps (m_vmmaps md)) -> Forall (fun z => fst q <> w64 (fst z)) D -> In q (vm_maps (m_vmmaps md')).

Lemma mkeep_maps : forall D md md', vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) -> mkeep D md md'.
Proof. intros D md md' E q Hq _. rewrite E. exact Hq. Qed.

Lemma mkeep_refl : forall D md, mkeep D md md.
Proof. intros D md. apply mkeep_maps. reflexivity. Qed.

Lemma mkeep_mono : forall D D' md md', incl D D' -> mkeep D md md' -> mkeep D' md md'.
Proof.
intros D D' md md' HI H q Hq HD. apply H; [exact Hq|]. apply Forall_forall. intros z Hz.
exact (proj1 (Forall_forall _ _) HD z (HI z Hz)).
Qed.

Lemma mkeep_nil_any : forall D md md', mkeep [] md md' -> mkeep D md md'.
Proof. intros D md md' H. apply (mkeep_mono [] D md md'); [intros z [] | exact H]. Qed.

Lemma mkeep_trans : forall D1 D2 md1 md2 md3, mkeep D1 md1 md2 -> mkeep D2 md2 md3 -> mkeep (D1 ++ D2) md1 md3.
Proof.
intros D1 D2 md1 md2 md3 H1 H2 q Hq HD. apply Forall_app in HD as [HD1 HD2]. exact (H2 q (H1 q Hq HD1) HD2).
Qed.

Lemma mkeep_nil_trans : forall md1 md2 md3, mkeep [] md1 md2 -> mkeep [] md2 md3 -> mkeep [] md1 md3.
Proof. intros md1 md2 md3 H1 H2. exact (mkeep_trans [] [] md1 md2 md3 H1 H2). Qed.

Lemma mkeep_wvb : forall D lazy mat md, mkeep D md (with_vm_backing lazy mat md).
Proof. intros D lazy mat md. apply mkeep_maps. reflexivity. Qed.

Lemma mkeep_sbm : forall D md md', same_but_materialized md md' -> mkeep D md md'.
Proof.
intros D md md' H. apply mkeep_maps. destruct (same_but_materialized_frame md md' H) as (_ & E & _). rewrite E. reflexivity.
Qed.

Lemma mkeep_mmap : forall D a n md, mkeep D md (YK0v.mmap_model a n md).
Proof.
intros D a n md q Hq _.
assert (E : vm_maps (m_vmmaps (YK0v.mmap_model a n md)) = (a, n) :: vm_maps (m_vmmaps md)) by reflexivity.
rewrite E. right. exact Hq.
Qed.

Lemma mmap_model_in : forall a n md, In (a, n) (vm_maps (m_vmmaps (YK0v.mmap_model a n md))).
Proof. intros a n md. left. reflexivity. Qed.

Lemma vm_maps_fixedin_ok : forall prot flags a n md,
vm_maps (m_vmmaps (YA05.fixedin_ok_model prot flags a n md)) = vm_maps (m_vmmaps md).
Proof.
intros prot flags a n md. unfold YA05.fixedin_ok_model, with_mmap_replacement.
rewrite YA09.with_mmap_backing_vmmaps. unfold YA05.fixedin_ok_vmmaps. destruct (Z.eqb prot 0); reflexivity.
Qed.

Lemma mkeep_fixedin_ok : forall D prot flags a n md, mkeep D md (YA05.fixedin_ok_model prot flags a n md).
Proof. intros D prot flags a n md. apply mkeep_maps. apply vm_maps_fixedin_ok. Qed.

Lemma mkeep_grant_md : forall D hole flags a n md, mkeep D md (YG0b.grant_md hole flags a n md).
Proof.
intros D hole flags a n md. unfold YG0b.grant_md. destruct hole.
- intros q Hq HD. rewrite YA09.with_mmap_backing_vmmaps. exact (mkeep_mmap D a n md q Hq HD).
- apply mkeep_fixedin_ok.
Qed.

Lemma mkeep_munmap : forall c m n md, mkeep [(c, m)] md (YK0v.munmap_model (w64 c) n md).
Proof.
intros c m n md q Hq HD. inversion HD as [|z l Hz _]; subst. cbn [fst] in Hz.
change (vm_maps (m_vmmaps (YK0v.munmap_model (w64 c) n md))) with (map_remove (vm_maps (m_vmmaps md)) (w64 c)).
unfold map_remove. apply filter_In. split; [exact Hq|].
destruct (bv_eqb (fst q) (w64 c)) eqn:E; [|reflexivity].
exfalso. apply Hz. apply bv_eqb_eq. exact E.
Qed.

(* The chain of c-asan's secondary-grant post model (AGif4.v's sec_md, whose flags are 50): the backing steps, the
   map of the secondary, and on a pointer-array grow the fixed map inside the reserved Q window. *)
Lemma mkeep_sec_chain : forall D (grow : bool) md0 mat matV mat' mb msz qs flags,
mkeep D md0
(let mdN := with_vm_backing (m_vm_lazy md0) mat md0 in
 let md2 := YK0v.mmap_model (w64 mb) (w64 msz) mdN in
 if grow
 then let mdV := with_vm_backing (m_vm_lazy md2) matV md2 in
      let md5 := YG0b.grant_md false flags (w64 qs) (w64 131072) mdV in
      with_vm_backing (m_vm_lazy md5) mat' md5
 else with_vm_backing (m_vm_lazy md2) mat' md2).
Proof.
intros D grow md0 mat matV mat' mb msz qs flags. apply mkeep_nil_any. cbv zeta. intros q Hq _.
destruct grow.
- apply (mkeep_wvb [] _ _ _ q); [|constructor]. apply (mkeep_grant_md [] _ _ _ _ _ q); [|constructor].
  apply (mkeep_wvb [] _ _ _ q); [|constructor]. apply (mkeep_mmap [] _ _ _ q); [|constructor].
  apply (mkeep_wvb [] _ _ _ q); [|constructor]. exact Hq.
- apply (mkeep_wvb [] _ _ _ q); [|constructor]. apply (mkeep_mmap [] _ _ _ q); [|constructor].
  apply (mkeep_wvb [] _ _ _ q); [|constructor]. exact Hq.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The generic keep and the base-apartness facts.                             *)
Lemma cfxm_w64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> w64 a = w64 b -> a = b.
Proof.
intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. unfold w64 in E.
rewrite !Z_to_bv_unsigned in E. rewrite !bv_wrap_small in E by (change (bv_modulus 64) with (2 ^ 64); lia). exact E.
Qed.

Lemma xs_mapped_cf_frame : forall ly S md ly' S' md' D,
xs_mapped_cf ly S md -> xs_cf ly' S' = xs_cf ly S -> mkeep D md md' ->
Forall (fun e => Forall (fun z => w64 (fst e) <> w64 (fst z)) D) (xs_cf ly S) ->
xs_mapped_cf ly' S' md'.
Proof.
intros ly S md ly' S' md' D Hm Ex Hk HD e He. rewrite Ex in He.
apply Hk; [exact (Hm e He)|]. exact (proj1 (Forall_forall _ _) HD e He).
Qed.

Lemma xs_mapped_cf_grow : forall ly S md ly' S' md',
xs_mapped_cf ly S md -> xs_cf ly' S' = xs_cf ly S -> mkeep [] md md' -> xs_mapped_cf ly' S' md'.
Proof.
intros ly S md ly' S' md' Hm Ex Hk. apply (xs_mapped_cf_frame ly S md ly' S' md' [] Hm Ex Hk).
apply Forall_forall. intros e _. constructor.
Qed.

(* An xs extent of a placed, mapped errbuf has a positive length (amwf: every map has one). *)
Lemma cfxm_xs_pos : forall ly S md, amwf md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
Forall (fun e => 4096 <= fst e /\ 0 < snd e /\ fst e + snd e <= alloc_ceiling) (xs_cf ly S).
Proof.
intros ly S md [_ MP] HP Hm. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) HP e He) as (_ & [I0 _] & UB & _).
pose proof (proj1 (Forall_forall _ _) (cfx_xs_snd_nonneg ly S) e He) as S0.
pose proof (MP _ (Hm e He)) as Hpos. pose proof alloc_ceiling_lt as CL.
destruct e as [b s]. unfold wiv, w64 in Hpos. cbn [fst snd] in *.
rewrite Z_to_bv_unsigned in Hpos. rewrite bv_wrap_small in Hpos by (change (bv_modulus 64) with (2 ^ 64); lia).
split; [exact I0|]. split; [exact Hpos | exact UB].
Qed.

(* Every sec extent of an ARcf state is placed (amc_placed) with a length of at least a page (Wf_cf). *)
Lemma cfxm_sec_ok : forall B ly S Hp rd, ARmcf B ly S Hp rd ->
Forall (fun z => 4096 <= fst z /\ 4096 <= snd z /\ fst z + snd z <= alloc_ceiling) (sec_extents ly S).
Proof.
intros B ly S Hp rd M. pose proof (amc_wf _ _ _ _ _ M) as W. pose proof (amc_placed _ _ _ _ _ M) as [PL _].
pose proof (sec_extents_sizes64P_cf _ 0 0 0 ly S W) as SZ.
apply Forall_forall. intros z Hz.
destruct (proj1 (Forall_forall _ _) PL z Hz) as (_ & [I0 _] & UB).
destruct (proj1 (Forall_forall _ _) SZ z Hz) as [Z1 _].
split; [exact I0|]. split; [exact Z1 | exact UB].
Qed.

(* The bases of the errbuf extent and of every sec extent differ: xs_placed_cf makes them disjoint, and both have a
   positive length. *)
Lemma xs_sec_apart : forall segs B ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> xs_placed_cf ly S ->
xs_mapped_cf ly S md -> forall e z, In e (xs_cf ly S) -> In z (sec_extents ly S) -> w64 (fst e) <> w64 (fst z).
Proof.
intros segs B ly S Hp W mem md (M & _ & _ & MW & _) HP Hm e z He Hz E.
pose proof (proj1 (Forall_forall _ _) (cfxm_xs_pos ly S md MW HP Hm) e He) as (E1 & E2 & E3).
pose proof (proj1 (Forall_forall _ _) (cfxm_sec_ok B ly S Hp _ M) z Hz) as (Z1 & Z2 & Z3).
pose proof (proj1 (Forall_forall _ _) HP e He) as (_ & _ & _ & D).
pose proof (proj1 (Forall_forall _ _) D z (in_or_app _ _ _ (or_introl Hz))) as Dz.
pose proof alloc_ceiling_lt as CL.
apply cfxm_w64_inj in E; [|lia|lia]. unfold zdisjoint in Dz. lia.
Qed.

(* The shadow band [kLowShadowBeg, kHighMemBeg) holds no xs base: an xs extent is in_app with a positive length. *)
Lemma xs_shadow_apart : forall ly S md c, amwf md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
kLowShadowBeg <= c < kHighMemBeg -> Forall (fun e => w64 (fst e) <> w64 c) (xs_cf ly S).
Proof.
intros ly S md c MW HP Hm Hc. apply Forall_forall. intros e He E.
pose proof (proj1 (Forall_forall _ _) (cfxm_xs_pos ly S md MW HP Hm) e He) as (E1 & E2 & E3).
pose proof (proj1 (Forall_forall _ _) HP e He) as (_ & [_ IA] & _ & _).
pose proof alloc_ceiling_lt as CL.
apply cfxm_w64_inj in E; [| lia | unfold kLowShadowBeg, kHighMemBeg in *; lia].
unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* A fresh grant's base is not an xs base: region_free puts it apart from every map, the xs extent among them. *)
Lemma errb_fresh_apart : forall ly S md a ncap, amwf md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
grant_ok_na_pin md (w64 a) ncap = true -> 0 <= a -> 0 < ncap -> a + ncap < 2 ^ 64 ->
Forall (fun z => w64 a <> w64 (fst z)) (xs_cf ly S).
Proof.
intros ly S md a ncap MW HP Hm Hg Ha Hn Han.
pose proof (xs_fresh_of_grant ly S md a ncap HP Hm Hg Ha ltac:(lia) Han) as FR.
apply Forall_forall. intros e He E.
pose proof (proj1 (Forall_forall _ _) (cfxm_xs_pos ly S md MW HP Hm) e He) as (E1 & E2 & E3).
pose proof (proj1 (Forall_forall _ _) FR e He) as D. pose proof alloc_ceiling_lt as CL.
apply cfxm_w64_inj in E; [|lia|lia]. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. The steps.                                                                   *)
Lemma xs_cf_secs : forall ly S S', st_secs S' = st_secs S -> xs_cf ly S' = xs_cf ly S.
Proof. intros ly S S' E. unfold xs_cf, errb_cap_cf, errb_e. rewrite E. reflexivity. Qed.

(* st_secs pointwise the same length and size (sec_dealloc's re-tag keeps both). *)
Lemma xs_cf_f2 : forall ly S S', Forall2 cfx_same_sm (st_secs S) (st_secs S') -> xs_cf ly S' = xs_cf ly S.
Proof.
intros ly S S' HS. unfold xs_cf, errb_cap_cf, errb_e.
rewrite (cfx_last_cap_idx_f2 _ _ HS 0 None).
rewrite (cfx_last_len_f2 _ _ (mkSec 0 ERRB_CAP_TAG false) (cfx_filter_f2 _ _ HS)). reflexivity.
Qed.

(* same_but_materialized keeps vm_maps (mkeep_sbm), so it keeps xs_mapped_cf: the form a law that re-establishes
   the relation at a materialized model takes (A/RGcfLaws.v rt_write's SBM). *)
Lemma xs_mapped_cf_sbm : forall ly S md md',
xs_mapped_cf ly S md -> same_but_materialized md md' -> xs_mapped_cf ly S md'.
Proof. intros ly S md md' Hm SBM. apply (xs_mapped_cf_grow ly S md ly S _ Hm eq_refl). exact (mkeep_sbm [] md md' SBM). Qed.

Lemma xs_mapped_cf_layout : forall ly ly' S md, layout_le (length (st_secs S)) ly ly' ->
xs_mapped_cf ly S md -> xs_mapped_cf ly' S md.
Proof. intros ly ly' S md LE Hm e He. rewrite (xs_cf_layout ly ly' S LE) in He. exact (Hm e He). Qed.

(* 3a. Map growth that leaves every map intact and st_secs as it is: KMapUser / KMapFreeArray / KMapPtrArray
       (grant_md), the backing steps, and populate_cf / map_more_user / ensure_free_array, which ask only those. *)
Lemma xs_mapped_cf_same_secs : forall ly S md ly' S' md', layout_le (length (st_secs S)) ly ly' ->
st_secs S' = st_secs S -> mkeep [] md md' -> xs_mapped_cf ly S md -> xs_mapped_cf ly' S' md'.
Proof.
intros ly S md ly' S' md' LE Es Hk Hm. apply (xs_mapped_cf_grow ly S md ly' S' md' Hm); [|exact Hk].
rewrite (xs_cf_secs ly' S S' Es). exact (xs_cf_layout ly ly' S LE).
Qed.

Lemma xs_mapped_cf_grant_md : forall ly S md hole flags a n,
xs_mapped_cf ly S md -> xs_mapped_cf ly S (YG0b.grant_md hole flags a n md).
Proof.
intros ly S md hole flags a n Hm. apply (xs_mapped_cf_grow ly S md ly S _ Hm eq_refl). apply mkeep_grant_md.
Qed.

Lemma xs_mapped_cf_wvb : forall ly S md lazy mat,
xs_mapped_cf ly S md -> xs_mapped_cf ly S (with_vm_backing lazy mat md).
Proof. intros ly S md lazy mat Hm. apply (xs_mapped_cf_grow ly S md ly S _ Hm eq_refl). apply mkeep_wvb. Qed.

(* ensure_free_array (the free-array growth of populate and of the free path's return_to_allocator) keeps st_secs on
   every path (cfx_same_ensure); the same for cgif's populate and map_more_user (class kBatchClass). *)
Lemma xs_cf_ensure_path : forall ly c need sof s t r, apath (ensure_free_array c need sof s) t r ->
xs_cf ly (snd r) = xs_cf ly s.
Proof.
intros ly c need sof s t r Hp. apply xs_cf_secs. exact (proj1 (cfx_ipost_apath _ _ t r (cfx_same_ensure c need sof s) Hp)).
Qed.

(* 3b. The secondary grant: sec_alloc appends a live non-capacity entry, the layout grows at the new index, the model
       only gains maps. *)
Lemma xs_mapped_cf_sec_grant : forall ly S md ly' S' md' sm, layout_le (length (st_secs S)) ly ly' ->
st_secs S' = st_secs S ++ [sm] -> is_errb_cap sm = false -> mkeep [] md md' ->
xs_mapped_cf ly S md -> xs_mapped_cf ly' S' md'.
Proof.
intros ly S md ly' S' md' sm LE Es Hn Hk Hm. apply (xs_mapped_cf_grow ly S md ly' S' md' Hm); [|exact Hk].
rewrite (xs_cf_app_noncap ly' S S' sm Es Hn). exact (xs_cf_layout ly ly' S LE).
Qed.

(* The same at c-asan's AIfaceS post model (AGif4.v's sec_md, unfolded). *)
Lemma xs_mapped_cf_sec_grant_chain : forall ly S md0 ly' S' sm (grow : bool) mat matV mat' mb msz qs flags,
layout_le (length (st_secs S)) ly ly' -> st_secs S' = st_secs S ++ [sm] -> is_errb_cap sm = false ->
xs_mapped_cf ly S md0 ->
xs_mapped_cf ly' S'
(let mdN := with_vm_backing (m_vm_lazy md0) mat md0 in
 let md2 := YK0v.mmap_model (w64 mb) (w64 msz) mdN in
 if grow
 then let mdV := with_vm_backing (m_vm_lazy md2) matV md2 in
      let md5 := YG0b.grant_md false flags (w64 qs) (w64 131072) mdV in
      with_vm_backing (m_vm_lazy md5) mat' md5
 else with_vm_backing (m_vm_lazy md2) mat' md2).
Proof.
intros ly S md0 ly' S' sm grow mat matV mat' mb msz qs flags LE Es Hn Hm.
exact (xs_mapped_cf_sec_grant ly S md0 ly' S' _ sm LE Es Hn (mkeep_sec_chain [] grow md0 mat matV mat' mb msz qs flags) Hm).
Qed.

(* 3c. The shadow remap (KShadowRemap). Its LPS step is a fixed map inside the shadow, grant_md false, which keeps
       every map. If a walk realizes part of it as an unmap instead, that unmap is based in the shadow band, which
       holds no xs base (xs_shadow_apart). *)
Lemma xs_mapped_cf_shadow_remap : forall ly S md flags a n,
xs_mapped_cf ly S md -> xs_mapped_cf ly S (YG0b.grant_md false flags a n md).
Proof. intros ly S md flags a n Hm. exact (xs_mapped_cf_grant_md ly S md false flags a n Hm). Qed.

Lemma xs_mapped_cf_shadow_frame : forall ly S md md' D, amwf md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
Forall (fun z => kLowShadowBeg <= fst z < kHighMemBeg) D -> mkeep D md md' -> xs_mapped_cf ly S md'.
Proof.
intros ly S md md' D MW HP Hm HD Hk. apply (xs_mapped_cf_frame ly S md ly S md' D Hm eq_refl Hk).
apply Forall_forall. intros e He. apply Forall_forall. intros z Hz.
exact (proj1 (Forall_forall _ _) (xs_shadow_apart ly S md (fst z) MW HP Hm (proj1 (Forall_forall _ _) HD z Hz)) e He).
Qed.

Lemma xs_mapped_cf_shadow_unmap : forall ly S md c n, amwf md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
kLowShadowBeg <= c < kHighMemBeg -> xs_mapped_cf ly S (YK0v.munmap_model (w64 c) n md).
Proof.
intros ly S md c n MW HP Hm Hc. apply (xs_mapped_cf_shadow_frame ly S md _ [(c, 0)] MW HP Hm).
- constructor; [exact Hc | constructor].
- apply mkeep_munmap.
Qed.

(* 3d. The secondary unmap at the quarantine recycle (sec_dealloc's KMunmapSec). The unmapped extent z is a sec
       extent of a reference state S0 (the call's start state, which still holds the recycled chunk) whose errbuf
       extent is the current one; the step itself changes neither the errbuf entry nor the layout below
       length st_secs. *)
Lemma xs_mapped_cf_sec_unmap : forall segs B ly S0 Hp W mem md0 S md ly' S' z n,
ARcf segs B ly S0 Hp W mem md0 -> xs_placed_cf ly S0 -> xs_mapped_cf ly S0 md0 ->
In z (sec_extents ly S0) -> xs_cf ly S = xs_cf ly S0 -> xs_cf ly' S' = xs_cf ly S ->
xs_mapped_cf ly S md -> xs_mapped_cf ly' S' (YK0v.munmap_model (w64 (fst z)) n md).
Proof.
intros segs B ly S0 Hp W mem md0 S md ly' S' z n HA HP Hm0 Hz E0 E1 Hm.
apply (xs_mapped_cf_frame ly S md ly' S' _ [(fst z, snd z)] Hm E1 (mkeep_munmap (fst z) (snd z) n md)).
rewrite E0. apply Forall_forall. intros e He. constructor; [|constructor].
exact (xs_sec_apart segs B ly S0 Hp W mem md0 HA HP Hm0 e z He Hz).
Qed.

(* sec_dealloc's own state step: the re-tag lupd r (mkSec (sm_len sm) (sm_size sm) false). *)
Lemma xs_cf_sec_dealloc : forall ly S S' r sm, nth_error (st_secs S) r = Some sm ->
st_secs S' = lupd (st_secs S) r (mkSec (sm_len sm) (sm_size sm) false) -> xs_cf ly S' = xs_cf ly S.
Proof. intros ly S S' r sm E Es. apply xs_cf_f2. rewrite Es. exact (cfx_f2_lupd _ _ _ E). Qed.

(* 3e. The class-full errbuf map / remap (errb_map_cf): every old capacity entry is retired and the new one appended at
       index length (st_secs S), whose ly_sec slot is the granted base; the new xs extent IS the new map. On a remap
       the runtime then unmaps the old buffer, which is based apart from the new one (errb_fresh_apart). *)
Lemma xs_mapped_cf_errb_map : forall S ly' S' ncap md',
st_secs S' = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] -> 0 <= ncap ->
In (wiv (ly_sec ly' (length (st_secs S)), ncap)) (vm_maps (m_vmmaps md')) -> xs_mapped_cf ly' S' md'.
Proof.
intros S ly' S' ncap md' Es Hn Hin e He. rewrite (xs_cf_remap ly' S S' ncap Es) in He.
destruct He as [<-|[]]. rewrite Z.max_r by exact Hn. exact Hin.
Qed.

Lemma xs_mapped_cf_errb_remap : forall S md ly' S' a ncap md1 D,
st_secs S' = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] -> 0 <= ncap ->
ly_sec ly' (length (st_secs S)) = a ->
mkeep D (YK0v.mmap_model (w64 a) (w64 ncap) md) md1 -> Forall (fun z => w64 a <> w64 (fst z)) D ->
xs_mapped_cf ly' S' md1.
Proof.
intros S md ly' S' a ncap md1 D Es Hn Ea Hk HD. apply (xs_mapped_cf_errb_map S ly' S' ncap md1 Es Hn).
rewrite Ea. apply Hk; [apply mmap_model_in | exact HD].
Qed.

(* The whole remap at the model: the grant at md (or at a backing step of it), the map, the backing steps, the
   munmap of the old buffer (based at the old xs base); premises ARcf's amwf and xs_placed_cf at the old state. *)
Lemma xs_mapped_cf_errb_remap_old : forall ly S md ly' S' a ncap md1 n,
amwf md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
grant_ok_na_pin md (w64 a) ncap = true -> 0 <= a -> 0 < ncap -> a + ncap < 2 ^ 64 ->
st_secs S' = map cfx_retire (st_secs S) ++ [mkSec ncap ERRB_CAP_TAG false] ->
ly_sec ly' (length (st_secs S)) = a -> mkeep [] (YK0v.mmap_model (w64 a) (w64 ncap) md) md1 ->
forall e, In e (xs_cf ly S) -> xs_mapped_cf ly' S' (YK0v.munmap_model (w64 (fst e)) n md1).
Proof.
intros ly S md ly' S' a ncap md1 n MW HP Hm Hg Ha Hn Han Es Ea Hk e He.
pose proof (errb_fresh_apart ly S md a ncap MW HP Hm Hg Ha Hn Han) as FA.
apply (xs_mapped_cf_errb_remap S md ly' S' a ncap _ ([] ++ [(fst e, snd e)]) Es ltac:(lia) Ea).
- exact (mkeep_trans [] _ _ _ _ Hk (mkeep_munmap (fst e) (snd e) n md1)).
- constructor; [exact (proj1 (Forall_forall _ _) FA e He) | constructor].
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The compositions.                                                            *)
(* 4a. All-paths posts that also see every request on the path.                   *)
Fixpoint cfxm_kpost {A : Type} (t : itree astate A) (Pq : kreq -> Prop) (P : A -> Prop) : Prop :=
match t with
| IRet a => P a
| IAsk q _ k => Pq q /\ forall z, cfxm_kpost (k z) Pq P
| ISpin _ => True
| IFail _ => True
end.

Lemma cfxm_kpost_mono {A} (t : itree astate A) : forall Pq (P Q : A -> Prop), (forall a, P a -> Q a) ->
cfxm_kpost t Pq P -> cfxm_kpost t Pq Q.
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [cfxm_kpost]; intros Pq P Q HPQ H.
- exact (HPQ a H).
- destruct H as [Hq Hk]. split; [exact Hq|]. intros z. exact (IH z Pq P Q HPQ (Hk z)).
- exact I.
- exact I.
Qed.

Lemma cfxm_kpost_ibind {A B0} (t : itree astate A) : forall (k : A -> itree astate B0) Pq (P : B0 -> Prop),
cfxm_kpost t Pq (fun a => cfxm_kpost (k a) Pq P) -> cfxm_kpost (ibind t k) Pq P.
Proof.
induction t as [a | q sn c IH | pc | f]; cbn [ibind cfxm_kpost]; intros k Pq P H.
- exact H.
- destruct H as [Hq Hk]. split; [exact Hq|]. intros z. apply IH. exact (Hk z).
- exact I.
- exact I.
Qed.

Lemma cfxm_kpost_ibind_assoc {A B0 C} (t : itree astate A) : forall (k1 : A -> itree astate B0) (k2 : B0 -> itree astate C) Pq P,
cfxm_kpost (ibind t (fun a => ibind (k1 a) k2)) Pq P -> cfxm_kpost (ibind (ibind t k1) k2) Pq P.
Proof.
induction t as [a | q sn c IH | pc | f]; cbn [ibind cfxm_kpost]; intros k1 k2 Pq P H.
- exact H.
- destruct H as [Hq Hk]. split; [exact Hq|]. intros z. apply IH. exact (Hk z).
- exact I.
- exact I.
Qed.

Lemma cfxm_kpost_apath {A : Type} : forall (t : itree astate A) Pq (P : A -> Prop) tr a, cfxm_kpost t Pq P ->
apath t tr a -> P a /\ Forall (fun qz => Pq (fst qz)) tr.
Proof.
induction t as [a' | q sn k IH | pc | f]; intros Pq P tr a H Hp; destruct tr as [|[q' z] tr];
cbn [apath cfxm_kpost] in Hp, H; try contradiction.
- subst a'. split; [exact H | constructor].
- destruct Hp as (-> & _ & Hp). destruct H as [Hq Hk]. destruct (IH z Pq P tr a (Hk z) Hp) as [HP HF].
  split; [exact HP | constructor; [exact Hq | exact HF]].
Qed.

Lemma cfxm_apath_ibind {A B0 : Type} : forall (t : itree astate A) (f : A -> itree astate B0) tr b,
apath (ibind t f) tr b -> exists tr1 tr2 a, tr = tr1 ++ tr2 /\ apath t tr1 a /\ apath (f a) tr2 b.
Proof.
induction t as [a | q sn k IH | pc | fl]; intros f tr b H; cbn [ibind] in H.
- exists [], tr, a. split; [reflexivity|]. split; [cbn [apath]; reflexivity | exact H].
- destruct tr as [|[q' z] tr]; cbn [apath] in H; [contradiction|].
  destruct H as (Eq & Ha & Hp). destruct (IH z f tr b Hp) as (tr1 & tr2 & a & -> & H1 & H2).
  exists ((q', z) :: tr1), tr2, a. split; [reflexivity|]. split; [|exact H2].
  cbn [apath]. split; [exact Eq|]. split; [exact Ha | exact H1].
- destruct tr; cbn [apath] in H; contradiction.
- destruct tr; cbn [apath] in H; contradiction.
Qed.

(* 4b. free_cf: the state frame cfx_fr (YGcfXs.v) and, at every KMunmapSec r, a chunk of the start state at index r. *)
Definition cfxm_secof (s0 : astate) (r : nat) : Prop :=
exists k o, In k (st_chunks s0) /\ ck_beg k = PSec r o.

Definition cfxm_uq (s0 : astate) (q : kreq) : Prop :=
match q with KMunmapSec r _ => cfxm_secof s0 r | _ => True end.

Create HintDb kmdb.

(* YGcfXs.v's fr_unf (section-local there). *)
Ltac km_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed, YG00.tick,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin, cfx_same in *).

Ltac km_cbn :=
cbn [ibind cfxm_kpost cfxm_uq fst snd st_secs st_chunks st_regions st_cache st_cache_inited st_sec_arr st_sec_reserved
st_qthread st_qglobal st_fs st_depot st_internal_inited st_nev set_regions set_cache set_chunks set_secs set_sec_arr
set_sec_reserved set_depot set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac km_hint :=
first
[ match goal with |- cfxm_kpost (ibind _ _) _ _ =>
  apply cfxm_kpost_ibind; eapply cfxm_kpost_mono; [|solve [eauto with kmdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in let H2 := fresh "Hc" in
  intros [x sx] [H1 H2]; cbn [fst snd] in H1, H2 end
| match goal with |- cfxm_kpost _ _ _ =>
  eapply cfxm_kpost_mono; [|solve [eauto with kmdb]];
  let x := fresh "x" in let sx := fresh "sx" in let H1 := fresh "Hs" in let H2 := fresh "Hc" in
  intros [x sx] [H1 H2]; cbn [fst snd] in H1, H2 end ].

Ltac km_step :=
first
[ progress km_cbn
| km_unf
| progress intros
| match goal with |- cfxm_kpost (ibind (ibind _ _) _) _ _ => apply cfxm_kpost_ibind_assoc end
| km_hint
| match goal with |- True /\ _ => split; [exact I|] end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| split; congruence ].

(* The callees that touch neither st_secs nor st_chunks, and ask no KMunmapSec. *)
Lemma km_same_ensure : forall s0 c need sof s,
cfxm_kpost (ensure_free_array c need sof s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c need sof s. unfold ensure_free_array. repeat km_step. Qed.
#[local] Hint Resolve km_same_ensure : kmdb.

Lemma km_same_mmu : forall s0 c need s, cfxm_kpost (map_more_user c need s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c need s. unfold map_more_user. repeat km_step. Qed.
#[local] Hint Resolve km_same_mmu : kmdb.

Lemma km_same_populate : forall s0 c need s, cfxm_kpost (populate c need s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c need s. unfold populate. repeat km_step. Qed.
#[local] Hint Resolve km_same_populate : kmdb.

Lemma km_same_gfa : forall s0 c n s, cfxm_kpost (get_from_allocator c n s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c n s. unfold get_from_allocator. repeat km_step. Qed.
#[local] Hint Resolve km_same_gfa : kmdb.

Lemma km_same_refill : forall s0 c s, cfxm_kpost (refill_if_empty c s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c s. unfold refill_if_empty. repeat km_step. Qed.
#[local] Hint Resolve km_same_refill : kmdb.

Lemma km_same_cache_alloc : forall s0 c s, cfxm_kpost (cache_alloc c s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c s. unfold cache_alloc. repeat km_step. Qed.
#[local] Hint Resolve km_same_cache_alloc : kmdb.

Lemma km_same_depot_put : forall s0 tr s, cfxm_kpost (depot_put tr s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 tr s. unfold depot_put. repeat km_step. Qed.
#[local] Hint Resolve km_same_depot_put : kmdb.

Lemma km_same_rta : forall s0 c offs s, cfxm_kpost (return_to_allocator c offs s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c offs s. unfold return_to_allocator. repeat km_step. Qed.
#[local] Hint Resolve km_same_rta : kmdb.

Lemma km_same_cache_dealloc : forall s0 c off s, cfxm_kpost (cache_dealloc c off s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 c off s. unfold cache_dealloc. repeat km_step. Qed.
#[local] Hint Resolve km_same_cache_dealloc : kmdb.

Lemma km_same_enqueue : forall s0 k s, cfxm_kpost (enqueue k s) (cfxm_uq s0) (fun r => cfx_same s (snd r)).
Proof. intros s0 k s. unfold enqueue. repeat km_step. Qed.
#[local] Hint Resolve km_same_enqueue : kmdb.

Lemma km_fr_ipost_same {A : Type} : forall (t : itree astate (A * astate)) s0 s Pq, cfx_fr s0 s ->
cfxm_kpost t Pq (fun r => cfx_same s (snd r)) -> cfxm_kpost t Pq (fun r => cfx_fr s0 (snd r)).
Proof.
intros t s0 s Pq H1 H2. eapply cfxm_kpost_mono; [|exact H2]. intros [x sx] [E1 E2]. cbn [snd] in *.
exact (cfx_fr_trans s0 s sx H1 (cfx_fr_same s sx E1 E2)).
Qed.

Lemma cfxm_mem_chunk_in : forall k l, mem_chunk k l = true -> exists k1, In k1 l /\ ck_beg k1 = ck_beg k.
Proof.
intros k l. induction l as [|k' t IH]; cbn [mem_chunk]; [discriminate|].
intros H. apply orb_true_iff in H as [H|H].
- apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _]. apply YG04.sptr_eqb_spec in H.
  exists k'. split; [left; reflexivity | exact H].
- destruct (IH H) as (k1 & Hk1 & E). exists k1. split; [right; exact Hk1 | exact E].
Qed.

Lemma km_fr_sec_dealloc : forall r s0 s, cfx_fr s0 s -> cfxm_secof s0 r ->
cfxm_kpost (sec_dealloc r s) (cfxm_uq s0) (fun x => cfx_fr s0 (snd x)).
Proof.
intros r s0 s H Hr. unfold sec_dealloc. km_unf. km_cbn.
destruct (nth_error (st_secs s) r) as [sm|] eqn:E; [|exact I].
destruct (index_of (st_sec_arr s) r 0) as [i|]; [|exact I].
repeat (first [progress km_cbn | km_unf | progress intros
| match goal with |- cfxm_kpost (ibind (ibind _ _) _) _ _ => apply cfxm_kpost_ibind_assoc end
| match goal with |- True /\ _ => split; [exact I|] end
| match goal with |- cfxm_secof _ _ /\ _ => split; [exact Hr|] end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I]).
all: eapply cfx_fr_dead; [exact H | exact E | reflexivity | reflexivity].
Qed.

Lemma km_fr_recycle_chunk : forall k s0 s, cfx_fr s0 s ->
cfxm_kpost (recycle_chunk k s) (cfxm_uq s0) (fun x => cfx_fr s0 (snd x)).
Proof.
intros k s0 s H. unfold recycle_chunk. km_unf. km_cbn.
destruct (mem_chunk k (st_chunks s)) eqn:Em; km_cbn; [|exact I].
assert (Hk : exists k0, In k0 (st_chunks s0) /\ ck_beg k0 = ck_beg k).
{ destruct (cfxm_mem_chunk_in k (st_chunks s) Em) as (k1 & Hk1 & Eb). destruct H as [_ HC].
  destruct (HC k1 Hk1) as (k0 & Hk0 & E0 & _). exists k0. split; [exact Hk0 | congruence]. }
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; km_cbn.
- exact I.
- eapply km_fr_ipost_same; [|apply km_same_cache_dealloc]. eapply cfx_fr_del; [exact H | reflexivity | reflexivity].
- apply km_fr_sec_dealloc; [eapply cfx_fr_del; [exact H | reflexivity | reflexivity]|].
  destruct Hk as (k0 & Hk0 & E0). exists k0, o. split; [exact Hk0 | congruence].
- exact I.
Qed.

Lemma km_fr_recycle_items : forall fuel items s0 s, cfx_fr s0 s ->
cfxm_kpost (recycle_items fuel items s) (cfxm_uq s0) (fun x => cfx_fr s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros items s0 s H; destruct items as [|k t]; cbn [recycle_items]; try km_unf; try km_cbn;
try exact H; try exact I.
apply cfxm_kpost_ibind. eapply cfxm_kpost_mono; [|exact (km_fr_recycle_chunk k s0 s H)].
intros [x sx] Hx. cbn [fst snd] in *. apply IH. exact Hx.
Qed.

Lemma km_fr_do_recycle : forall fuel bs s0 s, cfx_fr s0 s ->
cfxm_kpost (do_recycle fuel bs s) (cfxm_uq s0) (fun x => cfx_fr s0 (snd x)).
Proof.
induction fuel as [|f IH]; intros bs s0 s H; destruct bs as [|b t]; cbn [do_recycle]; try km_unf; try km_cbn;
try exact H; try exact I.
apply cfxm_kpost_ibind. eapply cfxm_kpost_mono; [|exact (km_fr_recycle_items 1100 (b_items b) s0 s H)].
intros [x sx] Hx. cbn [fst snd] in *.
apply cfxm_kpost_ibind.
eapply cfxm_kpost_mono; [|exact (km_fr_ipost_same _ s0 sx _ Hx (km_same_cache_dealloc s0 kBatchClass (b_self b) sx))].
intros [y sy] Hy. cbn [fst snd] in *. apply IH. exact Hy.
Qed.

Lemma km_fr_maybe_drain : forall s0 s, cfx_fr s0 s -> cfxm_kpost (maybe_drain_cf s) (cfxm_uq s0) (fun x => cfx_fr s0 (snd x)).
Proof.
intros s0 s H. unfold maybe_drain_cf.
repeat (first [progress km_cbn | km_unf | progress intros
| match goal with |- cfxm_kpost (ibind (ibind _ _) _) _ _ => apply cfxm_kpost_ibind_assoc end
| match goal with |- cfxm_kpost (do_recycle _ _ _) _ _ => apply km_fr_do_recycle end
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| assumption]).
Qed.

Lemma km_fr_free_cf : forall p tr S, cfxm_kpost (free_cf p tr S) (cfxm_uq S) (fun x => cfx_fr S (snd x)).
Proof.
intros p tr S. unfold free_cf.
repeat (first [progress km_cbn | km_unf | progress intros
| match goal with |- cfxm_kpost (ibind (recycle_chunk ?k ?s) _) _ _ =>
    apply cfxm_kpost_ibind; eapply cfxm_kpost_mono;
    [|apply (km_fr_recycle_chunk k S s); eapply cfx_fr_upd; [eassumption | km_cbn; congruence | km_cbn; congruence]];
    let x := fresh "x" in let sx := fresh "sx" in let H := fresh "Hr" in intros [x sx] H; cbn [fst snd] in H end
| match goal with |- cfxm_kpost (ibind (ibind _ _) _) _ _ => apply cfxm_kpost_ibind_assoc end
| match goal with |- cfxm_kpost (maybe_drain_cf _) _ _ => apply km_fr_maybe_drain end
| match goal with |- context [find_user ?l ?q] => let E := fresh "Ef" in destruct (find_user l q) eqn:E end
| km_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| (apply cfx_fr_same; reflexivity)
| (apply cfx_fr_same; congruence)
| (eapply cfx_fr_upd; [eassumption | congruence | congruence])
| assumption ]).
Qed.

(* The model lemma: on every path of free_cf, the state frame, and every KMunmapSec r names a secondary that a
   chunk of the start state holds. *)
Theorem free_cf_kpath : forall p tr S t S', apath (free_cf p tr S) t (tt, S') ->
cfx_fr S S' /\ Forall (fun qz => cfxm_uq S (fst qz)) t.
Proof.
intros p tr S t S' Hp. destruct (cfxm_kpost_apath _ _ _ t (tt, S') (km_fr_free_cf p tr S) Hp) as [HF HQ].
split; [exact HF | exact HQ].
Qed.

(* The extents a free path unmaps, at layout ly: one per KMunmapSec r len, based at ly_sec ly r. *)
Definition tr_unmaps (ly : alayout) (t : list (kreq * Z)) : list (Z * Z) :=
flat_map (fun qz => match fst qz with KMunmapSec r len => [(ly_sec ly r, len)] | _ => [] end) t.

Lemma tr_unmaps_sec : forall ly S t z, Forall (fun qz => cfxm_uq S (fst qz)) t -> In z (tr_unmaps ly t) ->
exists m, In (fst z, m) (sec_extents ly S).
Proof.
intros ly S t z HF Hz. unfold tr_unmaps in Hz. apply in_flat_map in Hz as ([q zz] & Hq & Hz).
pose proof (proj1 (Forall_forall _ _) HF _ Hq) as Hu. cbn [fst] in Hz, Hu.
destruct q as [c off len|c off len|off len|len|r len|base len|trc]; cbn [In] in Hz; try contradiction.
destruct Hz as [<-|[]]. cbn [cfxm_uq] in Hu. destruct Hu as (k & o & Hk & Eb).
exists (sec_map_size (ck_req k)). cbn [fst]. unfold sec_extents. apply in_flat_map.
exists k. split; [exact Hk|]. rewrite Eb. cbn [In]. left. reflexivity.
Qed.

(* THE FREE KEEP. The map frame is the walk's: every LPS step of the free path keeps every map except the munmap of
   sec_dealloc's KMunmapSec r len, at ly_sec ly r (layout_le pins ly_sec below length st_secs). *)
Theorem xs_mapped_cf_keep_free : forall segs B ly S Hp W mem md p tr t S' ly' md',
ARcf segs B ly S Hp W mem md -> xs_placed_cf ly S -> xs_mapped_cf ly S md ->
apath (free_cf p tr S) t (tt, S') -> layout_le (length (st_secs S)) ly ly' ->
mkeep (tr_unmaps ly t) md md' -> xs_mapped_cf ly' S' md'.
Proof.
intros segs B ly S Hp W mem md p tr t S' ly' md' HA HP Hm Hpath LE Hk.
destruct (free_cf_kpath p tr S t S' Hpath) as [[HS HC] HF].
destruct (free_frame_cf_of_state S S' HS HC) as [FX _].
apply (xs_mapped_cf_frame ly S md ly' S' md' (tr_unmaps ly t) Hm); [| exact Hk |].
- rewrite (FX ly'). exact (xs_cf_layout ly ly' S LE).
- apply Forall_forall. intros e He. apply Forall_forall. intros z Hz.
  destruct (tr_unmaps_sec ly S t z HF Hz) as (m & Hzm).
  exact (xs_sec_apart segs B ly S Hp W mem md HA HP Hm e (fst z, m) He Hzm).
Qed.

(* 4c. malloc_cf: the errbuf entry either stays (same last capacity index, same capacity) or is a fresh capacity
       entry at an index at or above the start's length st_secs. *)
Definition cfxm_xsr (s0 s : astate) : Prop :=
(length (st_secs s0) <= length (st_secs s))%nat /\
((last_cap_idx (st_secs s) 0 None = last_cap_idx (st_secs s0) 0 None /\ errb_cap_cf s = errb_cap_cf s0) \/
 (exists j, last_cap_idx (st_secs s) 0 None = Some j /\ (length (st_secs s0) <= j)%nat)).

Lemma cfxm_xsr_eq : forall s s', st_secs s' = st_secs s -> cfxm_xsr s s'.
Proof.
intros s s' E. split; [rewrite E; lia|]. left. split; [rewrite E; reflexivity|].
unfold errb_cap_cf, errb_e. rewrite E. reflexivity.
Qed.

Lemma cfxm_xsr_trans : forall s0 s1 s2, cfxm_xsr s0 s1 -> cfxm_xsr s1 s2 -> cfxm_xsr s0 s2.
Proof.
intros s0 s1 s2 [L1 [[I1 C1]|(j1 & J1 & K1)]] [L2 [[I2 C2]|(j2 & J2 & K2)]]; (split; [lia|]).
- left. split; congruence.
- right. exists j2. split; [exact J2 | lia].
- right. exists j1. split; [congruence | exact K1].
- right. exists j2. split; [exact J2 | lia].
Qed.

Lemma cfxm_xsr_app : forall s s' sm, st_secs s' = st_secs s ++ [sm] -> cfxm_xsr s s'.
Proof.
intros s s' sm Es. split; [rewrite Es, length_app; cbn [length]; lia|].
rewrite Es, cfx_last_cap_idx_app. cbn [last_cap_idx]. destruct (is_errb_cap sm) eqn:Hc.
- right. exists (0 + length (st_secs s))%nat. split; [reflexivity | lia].
- left. split; [reflexivity|]. unfold errb_cap_cf, errb_e. rewrite Es, filter_app.
  replace (filter is_errb_cap [sm]) with (@nil secmap) by (cbn [filter]; rewrite Hc; reflexivity).
  rewrite app_nil_r. reflexivity.
Qed.

Lemma cfxm_xsr_remap : forall s s' ncap, st_secs s' = map cfx_retire (st_secs s) ++ [mkSec ncap ERRB_CAP_TAG false] ->
cfxm_xsr s s'.
Proof.
intros s s' ncap Es. split; [rewrite Es, length_app, length_map; cbn [length]; lia|].
right. exists (0 + length (map cfx_retire (st_secs s)))%nat. rewrite Es, cfx_last_cap_idx_app. cbn [last_cap_idx].
split; [reflexivity | rewrite length_map; lia].
Qed.

(* errb_set_size's in-place update of the size entry: a non-capacity entry replaced by another. *)
Definition cfxm_capeq (a b : secmap) : Prop := is_errb_cap b = is_errb_cap a /\ (is_errb_cap a = true -> b = a).

Lemma cfxm_capeq_refl : forall l, Forall2 cfxm_capeq l l.
Proof. induction l as [|x t IH]; constructor; [split; [reflexivity | intros _; reflexivity] | exact IH]. Qed.

Lemma cfxm_capeq_idx : forall l l', Forall2 cfxm_capeq l l' -> forall i acc, last_cap_idx l' i acc = last_cap_idx l i acc.
Proof.
intros l l' H. induction H as [|x x' t t' [E _] Ht IH]; intros i acc; [reflexivity|].
cbn [last_cap_idx]. rewrite E. apply IH.
Qed.

Lemma cfxm_capeq_filter : forall l l', Forall2 cfxm_capeq l l' -> filter is_errb_cap l' = filter is_errb_cap l.
Proof.
intros l l' H. induction H as [|x x' t t' [E F] Ht IH]; [reflexivity|].
cbn [filter]. rewrite E. destruct (is_errb_cap x) eqn:Hx; [rewrite (F eq_refl), IH; reflexivity | exact IH].
Qed.

Lemma cfxm_capeq_lupd : forall l m x, is_errb_cap x = false ->
(forall sm, nth_error l m = Some sm -> is_errb_cap sm = false) -> Forall2 cfxm_capeq l (lupd l m x).
Proof.
induction l as [|y t IH]; intros m x Hx Hm; [destruct m; constructor|].
destruct m as [|m]; cbn [lupd].
- constructor; [|apply cfxm_capeq_refl]. pose proof (Hm y eq_refl) as Hy. split; [congruence | intros H; congruence].
- constructor; [split; [reflexivity | intros _; reflexivity] | apply IH; [exact Hx | intros sm H; exact (Hm sm H)]].
Qed.

Lemma cfxm_xsr_capeq : forall s s', Forall2 cfxm_capeq (st_secs s) (st_secs s') -> cfxm_xsr s s'.
Proof.
intros s s' H. split; [rewrite (Forall2_length H); lia|]. left. split; [apply cfxm_capeq_idx; exact H|].
unfold errb_cap_cf, errb_e. rewrite (cfxm_capeq_filter _ _ H). reflexivity.
Qed.

Lemma cfxm_find_sz : forall l k i, find_sz l k = Some i ->
(k <= i)%nat /\ exists sm, nth_error l (i - k) = Some sm /\ is_errb_sz sm = true.
Proof.
induction l as [|sm t IH]; intros k i H; cbn [find_sz] in H; [discriminate|].
revert H. destruct (is_errb_sz sm) eqn:E; intros H; cbv iota in H.
- injection H as <-. split; [lia|]. exists sm. rewrite Nat.sub_diag. split; [reflexivity | exact E].
- destruct (IH (S k) i H) as [Le (sm' & Hn & Hs)]. split; [lia|]. exists sm'.
  replace (i - k)%nat with (S (i - S k)) by lia. cbn [nth_error]. split; [exact Hn | exact Hs].
Qed.

Lemma cfxm_xsr_sz : forall s ns,
cfxm_xsr s (match find_sz (st_secs s) 0 with
| Some i => set_secs (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false)) s
| None => set_secs (st_secs s ++ [mkSec ns ERRB_SZ_TAG false]) s end).
Proof.
intros s ns. destruct (find_sz (st_secs s) 0) as [i|] eqn:E.
- apply cfxm_xsr_capeq. cbn [st_secs set_secs]. apply cfxm_capeq_lupd; [reflexivity|].
  intros sm Hsm. destruct (cfxm_find_sz _ _ _ E) as [_ (sm' & Hn & Hs)]. rewrite Nat.sub_0_r in Hn.
  rewrite Hn in Hsm. injection Hsm as <-. unfold is_errb_sz in Hs. unfold is_errb_cap.
  apply Z.eqb_eq in Hs. rewrite Hs. reflexivity.
- eapply cfxm_xsr_app. reflexivity.
Qed.

Create HintDb xmdb.

Ltac xm_unf :=
progress (unfold YG00.get_region, YG00.set_region, YG00.get_pc, YG00.set_pc, YG00.init_cache_if_needed, YG00.tick,
YG00.bind, YG00.get, YG00.put, YG00.modify, YG00.askz, YG00.ret, YG00.mcheck, YG00.fail, YG00.spin,
set_exh_cf, clear_exh_cf in *).

Ltac xm_cbn :=
cbn [ibind cfx_ipost fst snd st_secs st_chunks st_regions st_cache st_cache_inited st_sec_arr st_sec_reserved
st_qthread st_qglobal st_fs st_depot st_internal_inited st_nev set_regions set_cache set_chunks set_secs set_sec_arr
set_sec_reserved set_depot set_cache_inited set_nev set_qglobal set_qthread set_internal_inited] in *.

Ltac xm_close :=
match goal with H : cfxm_xsr ?a ?b |- cfxm_xsr ?a ?c =>
  first [ exact H
        | exact (cfxm_xsr_trans a b c H (cfxm_xsr_eq b c eq_refl))
        | (apply (cfxm_xsr_trans a b c H); eapply cfxm_xsr_app; reflexivity)
        | (apply (cfxm_xsr_trans a b c H); eapply cfxm_xsr_remap; reflexivity) ]
end.

#[local] Hint Extern 1 (cfxm_xsr _ _) => xm_close : xmdb.

Ltac xm_hint :=
match goal with
| H : cfxm_xsr ?a _ |- cfx_ipost (ibind _ _) _ =>
  apply cfx_ipost_ibind; eapply cfx_ipost_mono with (P := fun r => cfxm_xsr a (snd r)); [| solve [eauto with xmdb]];
  let x := fresh "x" in let sx := fresh "sx" in let Hx := fresh "Hx" in intros [x sx] Hx; cbn [fst snd] in Hx
| H : cfxm_xsr ?a _ |- cfx_ipost _ _ =>
  eapply cfx_ipost_mono with (P := fun r => cfxm_xsr a (snd r)); [| solve [eauto with xmdb]];
  let x := fresh "x" in let sx := fresh "sx" in let Hx := fresh "Hx" in intros [x sx] Hx; cbn [fst snd] in Hx
end.

Ltac xm_step :=
first
[ progress xm_cbn
| xm_unf
| progress intros
| match goal with |- cfx_ipost (ibind (ibind _ _) _) _ => apply cfx_ipost_ibind_assoc end
| xm_hint
| match goal with |- context [match ?x with _ => _ end] => destruct x end
| exact I
| xm_close ].

Lemma xm_of_same {A : Type} : forall (t : itree astate (A * astate)) s0 s, cfxm_xsr s0 s ->
cfx_ipost t (fun r => cfx_same s (snd r)) -> cfx_ipost t (fun r => cfxm_xsr s0 (snd r)).
Proof.
intros t s0 s H1 H2. eapply cfx_ipost_mono; [|exact H2]. intros [x sx] [E1 _]. cbn [snd] in *.
exact (cfxm_xsr_trans _ _ _ H1 (cfxm_xsr_eq s sx E1)).
Qed.

Lemma xm_ensure : forall c need sof s0 s, cfxm_xsr s0 s ->
cfx_ipost (ensure_free_array c need sof s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c need sof s0 s H. exact (xm_of_same _ s0 s H (cfx_same_ensure c need sof s)). Qed.
#[local] Hint Resolve xm_ensure : xmdb.

Lemma xm_mmu : forall c need s0 s, cfxm_xsr s0 s -> cfx_ipost (map_more_user c need s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c need s0 s H. exact (xm_of_same _ s0 s H (cfx_same_mmu c need s)). Qed.
#[local] Hint Resolve xm_mmu : xmdb.

Lemma xm_populate : forall c need s0 s, cfxm_xsr s0 s -> cfx_ipost (populate c need s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c need s0 s H. exact (xm_of_same _ s0 s H (cfx_same_populate c need s)). Qed.
#[local] Hint Resolve xm_populate : xmdb.

Lemma xm_depot_put : forall tr s0 s, cfxm_xsr s0 s -> cfx_ipost (depot_put tr s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros tr s0 s H. exact (xm_of_same _ s0 s H (cfx_same_depot_put tr s)). Qed.
#[local] Hint Resolve xm_depot_put : xmdb.

Lemma xm_errb_set_size : forall ns s0 s, cfxm_xsr s0 s -> cfx_ipost (errb_set_size ns s) (fun r => cfxm_xsr s0 (snd r)).
Proof.
intros ns s0 s H. unfold errb_set_size, YG00.modify. cbn [cfx_ipost snd].
exact (cfxm_xsr_trans _ _ _ H (cfxm_xsr_sz s ns)).
Qed.
#[local] Hint Resolve xm_errb_set_size : xmdb.

Lemma xm_errb_map : forall want s0 s, cfxm_xsr s0 s -> cfx_ipost (errb_map_cf want s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros want s0 s H. unfold errb_map_cf, errb_retire. repeat xm_step. Qed.
#[local] Hint Resolve xm_errb_map : xmdb.

Lemma xm_errb_append : forall len s0 s, cfxm_xsr s0 s -> cfx_ipost (errb_append_cf len s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros len s0 s H. unfold errb_append_cf. repeat xm_step. Qed.
#[local] Hint Resolve xm_errb_append : xmdb.

Lemma xm_errb_report : forall c s0 s, cfxm_xsr s0 s -> cfx_ipost (errb_report_cf c s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c s0 s H. unfold errb_report_cf. repeat xm_step. Qed.
#[local] Hint Resolve xm_errb_report : xmdb.

Lemma xm_mmu_cf : forall c need s0 s, cfxm_xsr s0 s -> cfx_ipost (map_more_user_cf c need s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c need s0 s H. unfold map_more_user_cf. repeat xm_step. Qed.
#[local] Hint Resolve xm_mmu_cf : xmdb.

Lemma xm_populate_cf : forall c need s0 s, cfxm_xsr s0 s -> cfx_ipost (populate_cf c need s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c need s0 s H. unfold populate_cf. repeat xm_step. Qed.
#[local] Hint Resolve xm_populate_cf : xmdb.

Lemma xm_gfa_cf : forall c n s0 s, cfxm_xsr s0 s -> cfx_ipost (get_from_allocator_cf c n s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c n s0 s H. unfold get_from_allocator_cf. repeat xm_step. Qed.
#[local] Hint Resolve xm_gfa_cf : xmdb.

Lemma xm_refill_cf : forall c s0 s, cfxm_xsr s0 s -> cfx_ipost (refill_if_empty_cf c s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c s0 s H. unfold refill_if_empty_cf. repeat xm_step. Qed.
#[local] Hint Resolve xm_refill_cf : xmdb.

Lemma xm_cache_alloc_cf : forall c s0 s, cfxm_xsr s0 s -> cfx_ipost (cache_alloc_cf c s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros c s0 s H. unfold cache_alloc_cf. repeat xm_step. Qed.
#[local] Hint Resolve xm_cache_alloc_cf : xmdb.

Lemma xm_sec_alloc : forall n s0 s, cfxm_xsr s0 s -> cfx_ipost (sec_alloc n s) (fun r => cfxm_xsr s0 (snd r)).
Proof. intros n s0 s H. unfold sec_alloc. repeat xm_step. Qed.
#[local] Hint Resolve xm_sec_alloc : xmdb.

Lemma xm_malloc_cf : forall n tr s, cfx_ipost (malloc_cf n tr s) (fun r => cfxm_xsr s (snd r)).
Proof.
intros n tr s. assert (H : cfxm_xsr s s) by (apply cfxm_xsr_eq; reflexivity). unfold malloc_cf. repeat xm_step.
Qed.

Lemma cfxm_xs_same_idx : forall ly s s', last_cap_idx (st_secs s') 0 None = last_cap_idx (st_secs s) 0 None ->
errb_cap_cf s' = errb_cap_cf s -> xs_cf ly s' = xs_cf ly s.
Proof. intros ly s s' Ei Ec. unfold xs_cf. rewrite Ei, Ec. reflexivity. Qed.

(* The model lemma: on every path of malloc_cf, the errbuf extent is the start's (at the grown layout), or the
   extent of a capacity entry this call appended. *)
Theorem malloc_cf_xs_path : forall n tr S t r ly ly', apath (malloc_cf n tr S) t r ->
layout_le (length (st_secs S)) ly ly' ->
xs_cf ly' (snd r) = xs_cf ly S \/
exists j, last_cap_idx (st_secs (snd r)) 0 None = Some j /\ (length (st_secs S) <= j)%nat /\
xs_cf ly' (snd r) = [(ly_sec ly' j, errb_cap_cf (snd r))].
Proof.
intros n tr S t r ly ly' Hp LE.
destruct (cfx_ipost_apath _ _ t r (xm_malloc_cf n tr S) Hp) as (_ & [[Ei Ec] | (j & Ej & Lj)]).
- left. rewrite (cfxm_xs_same_idx ly' S (snd r) Ei Ec). exact (xs_cf_layout ly ly' S LE).
- right. exists j. split; [exact Ej|]. split; [exact Lj|]. unfold xs_cf. rewrite Ej. reflexivity.
Qed.

(* The walk's map frame of a malloc call: if the call appended a capacity entry (a class-full map or remap), its slot
   is mapped at the end; if not, every map survives (malloc_cf asks no KMunmapSec, and the old buffer is unmapped
   only by a remap). *)
Definition xs_md_frame (ly' : alayout) (S S' : astate) (md md' : Model) : Prop :=
(forall j, last_cap_idx (st_secs S') 0 None = Some j -> (length (st_secs S) <= j)%nat ->
 In (wiv (ly_sec ly' j, errb_cap_cf S')) (vm_maps (m_vmmaps md'))) /\
((forall j, last_cap_idx (st_secs S') 0 None = Some j -> (j < length (st_secs S))%nat) -> mkeep [] md md').

(* THE MALLOC KEEP. No ARcf premise is needed: malloc_cf unmaps nothing but a superseded errbuf. *)
Theorem xs_mapped_cf_keep_malloc : forall ly S md n tr t r ly' md',
xs_mapped_cf ly S md -> apath (malloc_cf n tr S) t r -> layout_le (length (st_secs S)) ly ly' ->
xs_md_frame ly' S (snd r) md md' -> xs_mapped_cf ly' (snd r) md'.
Proof.
intros ly S md n tr t r ly' md' Hm Hp LE [F1 F2].
destruct (cfx_ipost_apath _ _ t r (xm_malloc_cf n tr S) Hp) as (_ & [[Ei Ec] | (j & Ej & Lj)]).
- apply (xs_mapped_cf_grow ly S md ly' (snd r) md' Hm).
  + rewrite (cfxm_xs_same_idx ly' S (snd r) Ei Ec). exact (xs_cf_layout ly ly' S LE).
  + apply F2. intros j Hj. rewrite Ei in Hj.
    pose proof (cfx_last_cap_idx_lt _ 0 None j Hj ltac:(intros k Hk; discriminate Hk)) as Hl. lia.
- intros e He. unfold xs_cf in He. rewrite Ej in He. destruct He as [<-|[]]. exact (F1 j Ej Lj).
Qed.

(* Discharging xs_md_frame. A path that appends no capacity entry (st_secs unchanged, or one non-capacity entry
   appended, as sec_alloc does) needs only the add-only frame; a class-full path whose last map is the errbuf slot
   needs that slot mapped. *)
Lemma xs_md_frame_same : forall ly' S S' md md',
(forall j, last_cap_idx (st_secs S') 0 None = Some j -> (j < length (st_secs S))%nat) -> mkeep [] md md' ->
xs_md_frame ly' S S' md md'.
Proof.
intros ly' S S' md md' Hn Hk. split; [|intros _; exact Hk].
intros j Hj Lj. pose proof (Hn j Hj). lia.
Qed.

Lemma cfxm_no_fresh_eq : forall S S', st_secs S' = st_secs S ->
forall j, last_cap_idx (st_secs S') 0 None = Some j -> (j < length (st_secs S))%nat.
Proof.
intros S S' E j Hj. rewrite E in Hj. pose proof (cfx_last_cap_idx_lt _ 0 None j Hj ltac:(intros k Hk; discriminate Hk)).
lia.
Qed.

Lemma cfxm_no_fresh_app : forall S S' sm, st_secs S' = st_secs S ++ [sm] -> is_errb_cap sm = false ->
forall j, last_cap_idx (st_secs S') 0 None = Some j -> (j < length (st_secs S))%nat.
Proof.
intros S S' sm E Hn j Hj. rewrite E, cfx_last_cap_idx_app in Hj. cbn [last_cap_idx] in Hj. rewrite Hn in Hj.
pose proof (cfx_last_cap_idx_lt _ 0 None j Hj ltac:(intros k Hk; discriminate Hk)). lia.
Qed.

Lemma xs_md_frame_fresh : forall ly' S S' md md' j, last_cap_idx (st_secs S') 0 None = Some j ->
(length (st_secs S) <= j)%nat -> In (wiv (ly_sec ly' j, errb_cap_cf S')) (vm_maps (m_vmmaps md')) ->
xs_md_frame ly' S S' md md'.
Proof.
intros ly' S S' md md' j Ej Lj Hin. split.
- intros j' Ej' _. rewrite Ej in Ej'. injection Ej' as <-. exact Hin.
- intros H. pose proof (H j Ej). lia.
Qed.

(* A secondary's st_secs entry (sec_alloc's mkSec map_size (needed_size n) true) is never a capacity entry:
   needed_size n >= 24 for every n. *)
Lemma cfxm_needed_size_pos : forall n, 0 < needed_size n.
Proof.
intros n. assert (R : 0 <= rz_log n)
by (unfold rz_log; repeat (match goal with |- context [if ?b then _ else _] => destruct b end); lia).
assert (RZ : 0 < rz_size n)
by (unfold rz_size; rewrite Z.shiftl_mul_pow2 by exact R; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) R); lia).
assert (RS : 0 < rounded_size n).
{ unfold rounded_size, round_up. pose proof (Z.le_max_r n 8) as H.
  assert (1 <= (Z.max n 8 + 8 - 1) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
unfold needed_size, needed_primary. destruct (from_primary n); lia.
Qed.

Lemma sec_entry_noncap : forall m n b, is_errb_cap (mkSec m (needed_size n) b) = false.
Proof.
intros m n b. unfold is_errb_cap. cbn [sm_size]. apply Z.eqb_neq. pose proof (cfxm_needed_size_pos n).
unfold ERRB_CAP_TAG. lia.
Qed.

(* The two path facts in YGcfAmx.v's ipost, the form atok_cf_ipost adds to an atok_cf post. *)
Lemma cfxm_ipost_amx {A} (t : itree astate A) : forall P, cfx_ipost t P -> YGcfAmx.ipost t P.
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [cfx_ipost YGcfAmx.ipost]; intros P H.
- exact H.
- intros z. exact (IH z P (H z)).
- exact I.
- exact I.
Qed.

Lemma cfxm_kpost_amx {A} (t : itree astate A) : forall Pq P, cfxm_kpost t Pq P -> YGcfAmx.ipost t P.
Proof.
induction t as [a | q sn k IH | pc | f]; cbn [cfxm_kpost YGcfAmx.ipost]; intros Pq P H.
- exact H.
- intros z. exact (IH z Pq P (proj2 H z)).
- exact I.
- exact I.
Qed.

Theorem malloc_cf_xs_ipost : forall n tr S, YGcfAmx.ipost (malloc_cf n tr S) (fun r => cfxm_xsr S (snd r)).
Proof. intros n tr S. exact (cfxm_ipost_amx _ _ (xm_malloc_cf n tr S)). Qed.

Theorem free_cf_fr_ipost : forall p tr S, YGcfAmx.ipost (free_cf p tr S) (fun x => cfx_fr S (snd x)).
Proof. intros p tr S. exact (cfxm_kpost_amx _ _ _ (km_fr_free_cf p tr S)). Qed.

(* 4d. realloc (ReallocP.realloc_tree_with at malloc_cf / free_cf): the entry step free_cf PNull, malloc_cf, and on a
       block the free of the old one. *)
Lemma realloc_tree_cf_inv : forall p n tr S t r,
apath (ReallocP.realloc_tree_with malloc_cf free_cf p n tr S) t r ->
exists t1 S1 t2 q S2, apath (free_cf PNull tr S) t1 (tt, S1) /\ apath (malloc_cf n tr S1) t2 (q, S2) /\
((q = PNull /\ r = (PNull, S2) /\ t = t1 ++ t2) \/
 (q <> PNull /\ exists t3 S3, apath (free_cf p tr S2) t3 (tt, S3) /\ r = (q, S3) /\ t = t1 ++ t2 ++ t3)).
Proof.
intros p n tr S t r H. unfold ReallocP.realloc_tree_with, YG00.bind in H. cbv beta in H.
apply cfxm_apath_ibind in H as (t1 & tt2 & [[] S1] & -> & H1 & H). cbv beta iota in H.
apply cfxm_apath_ibind in H as (t2 & t3 & [q S2] & -> & H2 & H). cbv beta iota in H.
exists t1, S1, t2, q, S2. split; [exact H1|]. split; [exact H2|].
destruct q as [|o|rr o|c x]; cbv beta iota delta [YG00.ret] in H;
[ left; destruct t3 as [|qz t3]; cbn [apath] in H; [|contradiction];
  subst r; split; [reflexivity|]; split; [reflexivity|]; rewrite app_nil_r; reflexivity
| .. ].
all: right; split; [discriminate|]; apply cfxm_apath_ibind in H as (t3a & t3b & [[] S3] & -> & H3 & H);
cbv beta iota delta [YG00.ret] in H; destruct t3b as [|qz t3b]; cbn [apath] in H; [|contradiction];
exists t3a, S3; split; [exact H3|]; split; [symmetry; exact H | rewrite app_nil_r; reflexivity].
Qed.

Lemma realloc_null_tree_cf_inv : forall n tr S t r,
apath (ReallocP.realloc_null_tree_with malloc_cf free_cf n tr S) t r ->
exists t1 S1 t2, apath (free_cf PNull tr S) t1 (tt, S1) /\ apath (malloc_cf n tr S1) t2 r /\ t = t1 ++ t2.
Proof.
intros n tr S t r H. unfold ReallocP.realloc_null_tree_with, YG00.bind in H. cbv beta in H.
apply cfxm_apath_ibind in H as (t1 & t2 & [[] S1] & -> & H1 & H2). cbv beta iota in H2.
exists t1, S1, t2. split; [exact H1|]. split; [exact H2 | reflexivity].
Qed.

(* The entry step free_cf PNull keeps the errbuf entry and length st_secs. *)
Lemma free_cf_xs_len : forall p tr S t S' ly, apath (free_cf p tr S) t (tt, S') ->
xs_cf ly S' = xs_cf ly S /\ length (st_secs S') = length (st_secs S).
Proof.
intros p tr S t S' ly Hp. destruct (free_cf_kpath p tr S t S' Hp) as [[HS HC] _].
destruct (free_frame_cf_of_state S S' HS HC) as [FX _].
split; [exact (FX ly) | symmetry; exact (Forall2_length HS)].
Qed.

(* realloc's head: the entry step and malloc_cf (realloc's NULL arm, and the whole of realloc(NULL, n)). *)
Theorem xs_mapped_cf_keep_realloc_head : forall ly S md n tr t1 S1 t2 r ly' md',
xs_mapped_cf ly S md -> apath (free_cf PNull tr S) t1 (tt, S1) -> apath (malloc_cf n tr S1) t2 r ->
layout_le (length (st_secs S)) ly ly' -> xs_md_frame ly' S1 (snd r) md md' -> xs_mapped_cf ly' (snd r) md'.
Proof.
intros ly S md n tr t1 S1 t2 r ly' md' Hm H1 H2 LE HF.
destruct (free_cf_xs_len PNull tr S t1 S1 ly H1) as [EX EL].
assert (Hm1 : xs_mapped_cf ly S1 md) by (intros e He; rewrite EX in He; exact (Hm e He)).
rewrite <- EL in LE. exact (xs_mapped_cf_keep_malloc ly S1 md n tr t2 r ly' md' Hm1 H2 LE HF).
Qed.

(* THE REALLOC KEEP, block arm: the head to the inner free's call (layout ly2, model md2), then the free of the old
   block. The free part's premises ARcf and xs_placed_cf are at that call, where RGtop's Deallocate pre (ARX) holds
   them; they are the free keep's own premises, at the state the free starts from. *)
Theorem xs_mapped_cf_keep_realloc : forall segs B ly S md p n tr t1 S1 t2 q S2 ly2 Hp2 W2 mem2 md2 t3 S3 ly' md',
xs_mapped_cf ly S md ->
apath (free_cf PNull tr S) t1 (tt, S1) -> apath (malloc_cf n tr S1) t2 (q, S2) -> apath (free_cf p tr S2) t3 (tt, S3) ->
layout_le (length (st_secs S)) ly ly2 -> xs_md_frame ly2 S1 S2 md md2 ->
ARcf segs B ly2 S2 Hp2 W2 mem2 md2 -> xs_placed_cf ly2 S2 ->
layout_le (length (st_secs S2)) ly2 ly' -> mkeep (tr_unmaps ly2 t3) md2 md' ->
xs_mapped_cf ly' S3 md'.
Proof.
intros segs B ly S md p n tr t1 S1 t2 q S2 ly2 Hp2 W2 mem2 md2 t3 S3 ly' md' Hm H1 H2 H3 LE2 HF2 HA2 HP2 LE3 Hk3.
pose proof (xs_mapped_cf_keep_realloc_head ly S md n tr t1 S1 t2 (q, S2) ly2 md2 Hm H1 H2 LE2 HF2) as Hm2.
exact (xs_mapped_cf_keep_free segs B ly2 S2 Hp2 W2 mem2 md2 p tr t3 S3 ly' md' HA2 HP2 Hm2 H3 LE3 Hk3).
Qed.

End XM.
