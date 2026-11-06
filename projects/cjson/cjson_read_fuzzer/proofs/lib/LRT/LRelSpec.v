(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma mmap_fixed_rw_outcome : forall addr len prot flags fd off i m o,
  mmap_off_aligned_b off = true ->
  mmap_anon_b flags = true ->
  w_is0 len = false ->
  mmap_modeled_b prot flags off = false ->
  mmap_noaccess_b prot flags off = false ->
  mmap_fixed_noaccess_b prot flags off = false ->
  mmap_fixed_rw_b prot flags off = true ->
  let h := m_vmmaps m in
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ <= alloc_top h)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  (0 < bv_unsigned addr)%Z ->
  region_free (vm_reserved h) addr n = true ->
  map_contains (vm_maps h) addr n = true ->
  mmap_spec addr len prot flags fd off i m o <->
  mmap_err_out m o
  \/ (mmap_fixed_rw_budget_ok flags m addr n = true
      /\ o = Ok (mkEffect addr [] [(addr, n)])
               (with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next h addr n) m)) [])
  \/ exists e, In e mmap_errnos /\
       o = Ok (mkEffectU (errno_ret e) [] [] [(addr, n)] [] [])
              (with_mmap_destroyed addr n (mmap_fixed_destroyed_next h addr n) m) [].
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfn Hfx. cbv zeta. intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfn, Hfx. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  assert (Hle : (bv_unsigned addr + page_round_up_Z (bv_unsigned len) <=? alloc_top (m_vmmaps m))%Z = true)
    by (apply Z.leb_le; exact Hce).
  rewrite E1. cbv iota. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys;
      rewrite ?Hle, ?(proj2 (Z.eqb_eq _ _) Hal), ?(proj2 (Z.ltb_lt _ _) Hpos) in *; cbn [negb] in *;
      rewrite ?Hrf, ?Hmc in *; cbn [andb] in *; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption| reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]]; eexists _, _, _, _; (split; [reflexivity|]);
      rewrite Hle, (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos); cbn [negb];
      rewrite Hrf, Hmc; cbn [andb]; (split; [|reflexivity]).
    + left. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. left. eexists _, _, _, _. split; [exists tt; split; [exact Hb|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
    + right. right. eexists _, _, _, _. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. eexists _, _, _, _. repeat split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma syscall_spec_233 : forall i m o,
  bv_unsigned (in_sysno i) = 233%Z ->
  syscall_spec i m o <-> madvise_spec (in_arg i 0) (in_arg i 1) (Syscall.int32 (in_arg i 2)) i m o.
Proof. intros i m o E; unfold syscall_spec, dispatch; rewrite E; reflexivity. Qed.

Lemma madvise_dontneed_outcome : forall addr len advice i m o,
  (bv_unsigned addr mod page_size = 0)%Z ->
  madvise_dontneed_b advice = true ->
  w_is0 len = false ->
  let nZ := page_round_up_Z (bv_unsigned len) in
  let n := Z_to_bv 64 nZ in
  (bv_unsigned addr + nZ < two_pow_64)%Z ->
  madvise_dontneed_ok (m_vmmaps m) addr n = true ->
  madvise_spec addr len advice i m o <->
  o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (madvise_dontneed_next m addr n) [].
Proof.
  intros addr len advice i m o Hal Hadv Hlen. cbv zeta. intros Hnw Hok. unfold madvise_spec.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), Hadv, Hlen. cbn [negb].
  rewrite (proj2 (Z.leb_gt _ _) Hnw). sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys; rewrite Hok in *; inv_sys. reflexivity.
  - intros ->. eexists _, _, _, _. split; [reflexivity|]. rewrite Hok.
    split; [|reflexivity]. eexists _, _, _, _. split; [reflexivity|]. split; reflexivity.
Qed.
