(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfLazyMaps.v, with its module paths changed. *)
(* Theorem Labs, 2026-10-30: ALedger_cf's alc_lazy_in_maps (YG0ncf.v), every noaccess or lazy address is mapped:
   its init witness and its keep lemmas over the model steps that touch vm_maps, vm_noaccess or m_vm_lazy
   (mmap_model, noaccess_model, with_mmap_backing, grant_md's two arms, munmap_model). Why (Main 2026-10-30,
   a Theorem Labs lane's RepF4Append 7th finding): nothing else in ARcf relates m_vm_lazy / vm_noaccess to vm_maps, so
   commit_expose's premise (no page of a fresh eager grant in m_vm_lazy) was unprovable at the Realloc walk.
   Reuse check (rule 24, LazyInMapsReuse): no layer, kit (7bb12afd3646) or LPS lemma states the lazy half; the
   noaccess half exists only as an assumed cs_ok field (YA0e.v:212 co_nasub). No function is proved here.
   Theorem Labs, 2026-10-30 (a Theorem Labs lane): the definition and its model-level keep lemmas moved to YKlazy.v, which
   Requires only YK* model files so that YA*'s start-up arms can call them; re-exported here. The two grant_md
   arms stay here (grant_md is YG0b's). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YK0v YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0g YG0b YA05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Export YKlazy.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The moved names keep this file's qualified names too (YGcfLazyMaps.<name>); the Export above gives the short ones. *)
Abbreviation lazy_in_maps_cf := YKlazy.lazy_in_maps_cf.
Abbreviation lim_cov_app := YKlazy.lim_cov_app.
Abbreviation lim_cov_cons := YKlazy.lim_cov_cons.
Abbreviation lazy_in_maps_init_cf := YKlazy.lazy_in_maps_init_cf.
Abbreviation lazy_in_maps_mmap_cf := YKlazy.lazy_in_maps_mmap_cf.
Abbreviation lazy_in_maps_noaccess_cf := YKlazy.lazy_in_maps_noaccess_cf.
Abbreviation lazy_in_maps_add_lazy_cf := YKlazy.lazy_in_maps_add_lazy_cf.
Abbreviation lazy_in_maps_backing_cf := YKlazy.lazy_in_maps_backing_cf.
Abbreviation lim_mmap_range := YKlazy.lim_mmap_range.
Abbreviation lazy_in_maps_noreserve_cf := YKlazy.lazy_in_maps_noreserve_cf.
Abbreviation lazy_in_maps_munmap_cf := YKlazy.lazy_in_maps_munmap_cf.

(* grant_md's hole arm (YG0b.v:27-28): the map, then its backing. *)
Lemma lazy_in_maps_grant_hole_cf : forall flags addr n md, lazy_in_maps_cf md ->
bv_unsigned addr + bv_unsigned n <= 2 ^ 64 -> lazy_in_maps_cf (YG0b.grant_md true flags addr n md).
Proof.
intros flags addr n md H Hb.
change (lazy_in_maps_cf (with_mmap_backing flags addr n (mmap_model addr n md))).
apply lazy_in_maps_backing_cf; [apply lazy_in_maps_mmap_cf; exact H | exact Hb | apply lim_mmap_range].
Qed.

(* grant_md's fixed-in arm (YA05.v:654-655 at prot 3): maps unchanged, [addr, addr + n) leaves the noaccess
   list (mmap_fixed_rw_next) and the lazy list (vm_forget_range), then the backing; the range must already be
   mapped (a MAP_FIXED inside a reservation). *)
Lemma lazy_in_maps_grant_fixed_cf : forall flags addr n md, lazy_in_maps_cf md ->
YK0g.ivs_wf (vm_noaccess (m_vmmaps md)) -> YK0g.ivs_wf (m_vm_lazy md) ->
bv_unsigned addr + bv_unsigned n <= 2 ^ 64 ->
(forall x, bv_unsigned addr <= x < bv_unsigned addr + bv_unsigned n -> YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
lazy_in_maps_cf (YG0b.grant_md false flags addr n md).
Proof.
intros flags addr n md H Wn Wl Hb HR.
assert (Hlh : bv_unsigned addr <= bv_unsigned addr + bv_unsigned n) by (pose proof (bv_unsigned_in_range 64 n); lia).
change (lazy_in_maps_cf (with_mmap_backing flags addr n
  (vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mmap_fixed_rw_next (m_vmmaps md) addr n) md)))).
apply lazy_in_maps_backing_cf; [| exact Hb | exact HR].
intros x Hx.
change (YK0g.covered (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
  ++ maps_subtract (m_vm_lazy md) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) x = true) in Hx.
change (YK0g.covered (vm_maps (m_vmmaps md)) x = true).
rewrite lim_cov_app, (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wn Hlh))),
  (proj2 (proj2 (YK0g.maps_subtract_sem _ _ _ Wl Hlh))) in Hx.
apply orb_true_iff in Hx as [Hx|Hx]; apply andb_true_iff in Hx as [Hx _]; apply H; rewrite lim_cov_app, Hx;
[reflexivity | apply orb_true_r].
Qed.
