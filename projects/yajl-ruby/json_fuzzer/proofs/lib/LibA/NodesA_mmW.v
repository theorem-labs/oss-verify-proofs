(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import KLiveCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanGap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel NodesA_mm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition mmap_CHK (addr len prot flags : Z) (mo : Model) (eff : SyscallEffect) : check_result :=
  check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo.

(* [comment removed for export] *)
Definition grant_rw (g nZ : Z) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 g) [] [(Z_to_bv 64 g, Z_to_bv 64 nZ)] [] [] [].
(* [comment removed for export] *)
Definition grant_none (g nZ : Z) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 g) [] [] [(Z_to_bv 64 g, Z_to_bv 64 nZ)] [] [].

Lemma mmap_errnos_ok : errnos_ok mmap_errnos = true.
Proof. reflexivity. Qed.

Section W.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Local Ltac head :=
  unfold mmap_CHK, check_mmap;
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true; cbn [negb];
  match goal with |- context [mmap_anon_b (Z_to_bv 64 ?f)] => change (mmap_anon_b (Z_to_bv 64 f)) with true; cbn [negb] end;
  rewrite w_is0_lit by lia;
  match goal with |- context [if (?l =? 0) then _ else _] => replace (l =? 0) with false by (symmetry; apply Z.eqb_neq; lia) end.

Lemma listNN_eqb_refl' : forall l, listNN_eqb l l = true.
Proof. intros l. apply (proj2 (listNN_eqb_eq l l)). reflexivity. Qed.

(* [comment removed for export] *)
Theorem mmap_grant_null_rw : forall len mo1,
  0 < len < 2^63 ->
  let h := m_vmmaps mo1 in let nZ := page_round_up_Z len in
  alloc_top h < 2^63 ->
  page_size + nZ + gap_weight nZ (vm_reserved h ++ vm_maps h) <= alloc_top h ->
  vm_backing_used mo1 + nZ <= vm_limit h ->
  exists eff mo', mmap_CHK 0 len 3 0x22 mo1 eff = CheckOk mo' [] /\ node_refusal (NMmap 0 len 3 0x22) mo1 (eff_ret eff) = false.
Proof.
  intros len mo1 Hlen h nZ HT HPS HB.
  assert (HnZ : 0 <= nZ) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  destruct (null_hint_window h nZ HnZ ltac:(lia) HPS) as (g & G1 & G2 & G3 & G4).
  exists (grant_rw g nZ). eexists. split.
  - head.
    change (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 0x22) (Z_to_bv 64 0)) with true. cbn [grant_rw].
    rewrite <- ret_in_errnos_errno_ret_in. rewrite (ret_in_errnos_lit mmap_errnos g mmap_errnos_ok) by lia.
    rewrite !unsigned_lit by lia. fold nZ.
    replace (g mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact G1).
    replace (0 <? g) with true by (symmetry; apply Z.ltb_lt; exact G2).
    replace (g + nZ <=? alloc_top (m_vmmaps mo1)) with true by (symmetry; apply Z.leb_le; exact G3).
    change (m_vmmaps mo1) with h. rewrite G4.
    unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 0x22)) with false.
    replace (vm_backing_used mo1 + nZ <=? vm_limit h) with true by (symmetry; apply Z.leb_le; exact HB).
    rewrite listNN_eqb_refl'. cbn [andb]. reflexivity.
  - cbn [node_refusal grant_rw eff_ret]. apply (ret_in_errnos_lit mmap_errnos g mmap_errnos_ok). lia.
Qed.

(* [comment removed for export] *)
Theorem mmap_grant_null_rw_lazy : forall len mo1,
  0 < len < 2^63 ->
  let h := m_vmmaps mo1 in let nZ := page_round_up_Z len in
  alloc_top h < 2^63 ->
  page_size + nZ + gap_weight nZ (vm_reserved h ++ vm_maps h) <= alloc_top h ->
  exists eff mo', mmap_CHK 0 len 3 0x4022 mo1 eff = CheckOk mo' [] /\ node_refusal (NMmap 0 len 3 0x4022) mo1 (eff_ret eff) = false.
Proof.
  intros len mo1 Hlen h nZ HT HPS.
  assert (HnZ : 0 <= nZ) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  destruct (null_hint_window h nZ HnZ ltac:(lia) HPS) as (g & G1 & G2 & G3 & G4).
  exists (grant_rw g nZ). eexists. split.
  - head.
    change (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 0x4022) (Z_to_bv 64 0)) with true. cbn [grant_rw].
    rewrite <- ret_in_errnos_errno_ret_in. rewrite (ret_in_errnos_lit mmap_errnos g mmap_errnos_ok) by lia.
    rewrite !unsigned_lit by lia. fold nZ.
    replace (g mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact G1).
    replace (0 <? g) with true by (symmetry; apply Z.ltb_lt; exact G2).
    replace (g + nZ <=? alloc_top (m_vmmaps mo1)) with true by (symmetry; apply Z.leb_le; exact G3).
    change (m_vmmaps mo1) with h. rewrite G4.
    unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 0x4022)) with true.
    rewrite listNN_eqb_refl'. cbn [andb]. reflexivity.
  - cbn [node_refusal grant_rw eff_ret]. apply (ret_in_errnos_lit mmap_errnos g mmap_errnos_ok). lia.
Qed.

(* [comment removed for export] *)
Theorem mmap_grant_null_none_lazy : forall len mo1,
  0 < len < 2^63 ->
  let h := m_vmmaps mo1 in let nZ := page_round_up_Z len in
  alloc_top h < 2^63 ->
  page_size + nZ + gap_weight nZ (vm_reserved h ++ vm_maps h) <= alloc_top h ->
  exists eff mo', mmap_CHK 0 len 0 0x4022 mo1 eff = CheckOk mo' [] /\ node_refusal (NMmap 0 len 0 0x4022) mo1 (eff_ret eff) = false.
Proof.
  intros len mo1 Hlen h nZ HT HPS.
  assert (HnZ : 0 <= nZ) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
  destruct (null_hint_window h nZ HnZ ltac:(lia) HPS) as (g & G1 & G2 & G3 & G4).
  exists (grant_none g nZ). eexists. split.
  - head.
    change (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 0x4022) (Z_to_bv 64 0)) with false.
    change (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 0x4022) (Z_to_bv 64 0)) with true. cbn [grant_none].
    rewrite <- ret_in_errnos_errno_ret_in. rewrite (ret_in_errnos_lit mmap_errnos g mmap_errnos_ok) by lia.
    rewrite !unsigned_lit by lia. fold nZ.
    replace (g mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact G1).
    replace (0 <? g) with true by (symmetry; apply Z.ltb_lt; exact G2).
    replace (g + nZ <=? alloc_top (m_vmmaps mo1)) with true by (symmetry; apply Z.leb_le; exact G3).
    change (m_vmmaps mo1) with h. rewrite G4.
    rewrite listNN_eqb_refl'. cbn [andb]. reflexivity.
  - cbn [node_refusal grant_none eff_ret]. apply (ret_in_errnos_lit mmap_errnos g mmap_errnos_ok). lia.
Qed.

(* [comment removed for export] *)
Definition grant_fixed_rw (A nZ : Z) : SyscallEffect :=
  mkEffectU (Z_to_bv 64 A) [] [(Z_to_bv 64 A, Z_to_bv 64 nZ)] [] [] [].

(* [comment removed for export] *)
Theorem mmap_grant_fixed_rw : forall A len flags mo1,
  (flags = 0x32 \/ flags = 0x4032) ->
  0 < len < 2^63 ->
  let h := m_vmmaps mo1 in let nZ := page_round_up_Z len in
  A mod page_size = 0 -> 0 < A -> A + nZ <= alloc_top h -> alloc_top h < 2^63 ->
  region_free (vm_reserved h) (Z_to_bv 64 A) (Z_to_bv 64 nZ) = true ->
  map_contains (vm_maps h) (Z_to_bv 64 A) (Z_to_bv 64 nZ) = true ->
  mmap_fixed_rw_budget_ok (Z_to_bv 64 flags) mo1 (Z_to_bv 64 A) (Z_to_bv 64 nZ) = true ->
  exists eff mo', mmap_CHK A len 3 flags mo1 eff = CheckOk mo' [] /\ node_refusal (NMmap A len 3 flags) mo1 (eff_ret eff) = false.
Proof.
  intros A len flags mo1 Hfl Hlen h nZ HA1 HA2 HA3 HT HRF HMC HB.
  assert (HnZ : len <= nZ) by (unfold nZ, page_round_up_Z; Z.div_mod_to_equations; lia).
  exists (grant_fixed_rw A nZ). eexists. split.
  - unfold mmap_CHK, check_mmap.
    change (mmap_off_aligned_b (Z_to_bv 64 0)) with true; cbn [negb].
    replace (mmap_anon_b (Z_to_bv 64 flags)) with true by (destruct Hfl as [-> | ->]; reflexivity). cbn [negb].
    rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (mmap_modeled_b (Z_to_bv 64 3) (Z_to_bv 64 flags) (Z_to_bv 64 0)) with false by (destruct Hfl as [-> | ->]; reflexivity).
    replace (mmap_noaccess_b (Z_to_bv 64 3) (Z_to_bv 64 flags) (Z_to_bv 64 0)) with false by (destruct Hfl as [-> | ->]; reflexivity).
    replace (mmap_fixed_noaccess_b (Z_to_bv 64 3) (Z_to_bv 64 flags) (Z_to_bv 64 0)) with false by (destruct Hfl as [-> | ->]; reflexivity).
    replace (mmap_fixed_rw_b (Z_to_bv 64 3) (Z_to_bv 64 flags) (Z_to_bv 64 0)) with true by (destruct Hfl as [-> | ->]; reflexivity).
    cbv zeta. rewrite !unsigned_lit by lia. fold nZ.
    replace (two_pow_64 <=? A + nZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
    replace (A + nZ <=? alloc_top (m_vmmaps mo1)) with true by (symmetry; apply Z.leb_le; exact HA3). cbn [negb].
    replace (A mod page_size =? 0) with true by (symmetry; apply Z.eqb_eq; exact HA1). cbn [negb].
    replace (0 <? A) with true by (symmetry; apply Z.ltb_lt; exact HA2). cbn [negb].
    change (m_vmmaps mo1) with h. rewrite HRF, HMC. cbn [andb grant_fixed_rw].
    rewrite <- ret_in_errnos_errno_ret_in. rewrite (ret_in_errnos_lit mmap_errnos A mmap_errnos_ok) by lia.
    rewrite bv_eqb_refl, listNN_eqb_refl', HB. reflexivity.
  - cbn [node_refusal grant_fixed_rw eff_ret]. apply (ret_in_errnos_lit mmap_errnos A mmap_errnos_ok). lia.
Qed.

(* [comment removed for export] *)
Lemma LI_backing_room : forall (S : word -> Prop) N EB mo nZ,
  LI S N EB mo -> EB + Z.of_nat N * page_size + nZ <= vm_limit (m_vmmaps mo) ->
  vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo).
Proof.
  intros S N EB mo nZ HLI Hc. rewrite vm_backing_used_split.
  pose proof (li_eager _ _ _ _ HLI) as He.
  pose proof (li_cap _ _ _ _ HLI (m_vm_materialized mo) (li_nodup _ _ _ _ HLI) (li_inS _ _ _ _ HLI)) as Hn.
  unfold page_size in *. nia.
Qed.

End W.
