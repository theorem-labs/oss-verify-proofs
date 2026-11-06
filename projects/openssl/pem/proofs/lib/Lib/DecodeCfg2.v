(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import CfgStep.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode NodesCfg DecodeCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithCeiling.
Context {CE : Ceiling}.

Lemma nstep_mprotect_rw_safe : forall addr mo rsp mo' evs,
  (0 <= addr)%Z -> (addr + 4096 < 2^64)%Z -> (addr mod 4096 = 0)%Z ->
  Nodes.nstep (NMprotect addr 4096 3) mo rsp mo' evs ->
  mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 4096) (Z_to_bv 64 3) (m_vmmaps mo) = true.
Proof.
  intros addr mo rsp mo' evs Ha0 Ha1 Hal H.
  apply Nodes.nstep_mprotect_iff in H. unfold check_mprotect in H. unfold mprotect_safe_b.
  change (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false in *. cbv iota in *.
  rewrite (unsigned_lit addr) in * by lia. change page_size with 4096%Z in *. rewrite Hal in *. cbn [negb Z.eqb] in *.
  rewrite w_is0_lit in * by lia. change (4096 =? 0)%Z with false in *. cbv iota in *.
  rewrite (unsigned_lit 4096) in * by lia. change (page_round_up_Z 4096) with 4096%Z in *.
  replace (two_pow_64 <=? addr + 4096)%Z with false in * by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia).
  change (mprotect_modeled_b (Z_to_bv 64 3)) with true in *. cbn [negb] in H. cbv iota zeta in *.
  destruct (map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 4096)
            && map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 4096)); [reflexivity|].
  cbn [orb].
  destruct (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 4096)
            && region_free (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 4096)); [reflexivity| discriminate H].
Qed.

(* [comment removed for export] *)
Lemma nstep_c_mprotect_noerr' : forall addr mo rsp mo' evs,
  (0 <= addr)%Z -> (addr + 4096 < 2^64)%Z -> (addr mod 4096 = 0)%Z ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 4096) = true ->
  nstep_c (NMprotect addr 4096 3) mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros addr mo rsp mo' evs Ha0 Ha1 Hal Hbud Hc.
  apply (nstep_c_mprotect_noerr addr mo rsp mo' evs Ha0 Ha1 Hal Hbud); [| exact Hc].
  exact (nstep_mprotect_rw_safe addr mo rsp mo' evs Ha0 Ha1 Hal (nstep_c_nstep _ _ _ _ _ Hc)).
Qed.

(* [comment removed for export] *)
Lemma node_decided_mmap_anon : forall len prot mo,
  (0 < len)%Z -> (mmap_len len < 2^64)%Z -> prot = 0%Z \/ prot = 3%Z ->
  (if (prot =? 0)%Z then mmap_reserve_refusable mo (mmap_len len)
   else mmap_grant_refusable (Z_to_bv 64 34) mo (mmap_len len)) = false ->
  node_decided (NMmap 0 len prot 34) mo.
Proof.
  intros len prot mo H1 H2 H3 H4. destruct (grant_exists_mmap_anon len prot mo H1 H2 H3 H4) as (eff & mo' & evs & Hn & Hr).
  exact (node_decided_of_grant _ _ eff mo' evs Hn Hr).
Qed.

Lemma node_decided_mprotect_rw : forall addr mo,
  (0 <= addr)%Z -> (addr + 4096 < 2^64)%Z -> (addr mod 4096 = 0)%Z ->
  mprotect_budget_ok mo (Z_to_bv 64 addr) (Z_to_bv 64 4096) = true ->
  mprotect_safe_b (Z_to_bv 64 addr) (Z_to_bv 64 4096) (Z_to_bv 64 3) (m_vmmaps mo) = true ->
  node_decided (NMprotect addr 4096 3) mo.
Proof.
  intros addr mo H1 H2 H3 H4 H5. destruct (grant_exists_mprotect_rw addr mo H1 H2 H3 H4 H5) as (eff & mo' & evs & Hn & Hr).
  exact (node_decided_of_grant _ _ eff mo' evs Hn Hr).
Qed.

Lemma node_decided_mmap_fixed_none : forall a mo,
  let h := m_vmmaps mo in let aw := Z_to_bv 64 a in let n := Z_to_bv 64 4096 in
  (0 < a)%Z -> (a + 4096 <= alloc_top h)%Z -> (a mod 4096 = 0)%Z ->
  region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
  node_decided (NMmap a 4096 0 50) mo.
Proof.
  intros a mo h aw n H1 H2 H3 H4 H5. destruct (grant_exists_mmap_fixed_none a mo H1 H2 H3 H4 H5) as (eff & mo' & evs & Hn & Hr).
  exact (node_decided_of_grant _ _ eff mo' evs Hn Hr).
Qed.

End WithCeiling.
