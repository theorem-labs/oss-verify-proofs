(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs VmMapsDisjoint.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require MmapSim RefNodes AsanCeil.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.KStep. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrRoom. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrAccSpec. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Mr Require Import MrAcc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition none_next (h : VmMaps) (a n : word) : VmMaps :=
  mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Lemma nstep_mmap_none_grant : forall len mo (a : word),
  0 < len < 2^63 ->
  RefNodes.grant_ok_na (Z_to_bv 64 0) mo a (page_round_up_Z len) = true ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  nstep (NMmap 0 len PROT_NONE MAPF) mo (mkEffectU a [] [] [(a, n)] [] [])
        (with_vmmaps (none_next (m_vmmaps mo) a n) mo) [].
Proof.
  intros len mo a Hlen Hg n.
  assert (Hn0 : 0 <= page_round_up_Z len) by (apply page_round_up_Z_nonneg; lia).
  unfold RefNodes.grant_ok_na in Hg.
  (* a worker port727 (): grant_ok_na = Linux's placement && the four ledger facts && the hint check; the
     noaccess arm grants exactly the placed address, after the decline gate the NULL hint never takes. *)
  apply andb_prop in Hg as [Hg Hhint]. apply andb_prop in Hg as [Hg Hfree]. apply andb_prop in Hg as [Hg Htop].
  apply andb_prop in Hg as [Hg Hpos]. apply andb_prop in Hg as [Hplace Hal].
  assert (Hne : errno_ret_in mmap_errnos a = false).
  { apply errno_ret_in_below; [reflexivity|]. apply Z.leb_le in Htop. alloc_top_bounds. unfold two_pow_64 in *. lia. }
  apply nstep_mmap_nr; [reflexivity | | exact Hne].
  unfold check_mmap.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. change (mmap_anon_b (Z_to_bv 64 MAPF)) with true. cbn [negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with false.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
  replace (place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 0) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
    with false by reflexivity.
  rewrite Hne. rewrite (unsigned_lit len) by lia. cbv zeta.
  rewrite Hplace. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
  unfold with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbv iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_none_grant_exists : forall B len mo,
  room B mo -> 0 < len -> page_round_up_Z len <= 2 ^ 30 -> len < 2 ^ 63 ->
  exists a, RefNodes.grant_ok_na (Z_to_bv 64 0) mo a (page_round_up_Z len) = true.
Proof.
  intros B len mo (Hisp & Hsz & Hcnt & _) Hlen Hr Hlt.
  assert (Hn0 : 0 <= page_round_up_Z len) by (apply page_round_up_Z_nonneg; lia).
  (* a worker port727 (): Linux's placement takes a positive, page-aligned length. *)
  assert (Hr0 : 0 < page_round_up_Z len) by (apply AsanCeil.page_round_up_Z_pos'; lia).
  assert (Hral : page_round_up_Z len mod page_size = 0) by (unfold page_round_up_Z; apply Z_mod_mult).
  apply RefNodes.grant_exists_na; try assumption; lia.
Qed.

Lemma m_vmmaps_none_next : forall mo a n, m_vmmaps (with_vmmaps (none_next (m_vmmaps mo) a n) mo) = none_next (m_vmmaps mo) a n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nstep_mprotect_rw_grant : forall p mo,
  0 < p < 2^63 -> p mod page_size = 0 ->
  map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true ->
  MrAccSpec.mapped mo <= vm_limit (m_vmmaps mo) ->
  (* a worker port727 (): check_mprotect answers unmodeled for a range that meets the vDSO pair. *)
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (Z_to_bv 64 p) (Z_to_bv 64 4096) = true ->
  nstep (NMprotect p 4096 PROT_RW) mo (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 p, Z_to_bv 64 4096)] [] [] [])
        (mprotect_model_next mo (Z_to_bv 64 p) (Z_to_bv 64 4096)) [].
Proof.
  intros p mo Hp Hal Hna Hmp Hbud Hvd.
  apply nstep_mprotect_nr; [| reflexivity]. unfold check_mprotect.
  change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. cbv iota.
  rewrite (unsigned_lit p) by lia. rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb]. cbv iota.
  change (w_is0 (Z_to_bv 64 4096)) with false. cbv iota.
  change (bv_unsigned (Z_to_bv 64 4096)) with 4096. change (page_round_up_Z 4096) with 4096.
  replace (two_pow_64 <=? p + 4096) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia). cbv iota.
  change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true. cbn [negb]. cbv iota zeta.
  rewrite Hvd. cbn [negb]. cbv iota.
  rewrite Hna, Hmp. cbn [andb]. cbv iota.
  change (errno_ret_in mprotect_errnos (Z_to_bv 64 0)) with false. cbv iota.
  assert (Hb : mprotect_budget_ok mo (Z_to_bv 64 p) (Z_to_bv 64 4096) = true).
  { unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
    pose proof (MrAccSpec.backing_le_mapped (mprotect_model_next mo (Z_to_bv 64 p) (Z_to_bv 64 4096))) as Hle.
    assert (Hm : MrAccSpec.mapped (mprotect_model_next mo (Z_to_bv 64 p) (Z_to_bv 64 4096)) = MrAccSpec.mapped mo) by reflexivity.
    assert (Hl : vm_limit (m_vmmaps (mprotect_model_next mo (Z_to_bv 64 p) (Z_to_bv 64 4096))) = vm_limit (m_vmmaps mo)) by reflexivity.
    rewrite Hl. lia. }
  rewrite Hb. change (w_is0 (Z_to_bv 64 0)) with true. cbn [andb].
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma none_next_contains_page2 : forall h (a : word),
  bv_unsigned a + 8192 < 2 ^ 64 ->
  let h' := none_next h a (Z_to_bv 64 8192) in
  map_contains (vm_noaccess h') (Z_to_bv 64 (bv_unsigned a + 4096)) (Z_to_bv 64 4096) = true /\
  map_contains (vm_maps h') (Z_to_bv 64 (bv_unsigned a + 4096)) (Z_to_bv 64 4096) = true.
Proof.
  intros h a Ha h'. pose proof (word_range a) as Hr.
  assert (E : forall rest, map_contains ((a, Z_to_bv 64 8192) :: rest) (Z_to_bv 64 (bv_unsigned a + 4096)) (Z_to_bv 64 4096) = true).
  { intro rest. unfold map_contains. cbn [existsb fst snd].
    rewrite (VmMapsDisjoint.u64 (bv_unsigned a + 4096)) by lia.
    change (bv_unsigned (Z_to_bv 64 8192)) with 8192. change (bv_unsigned (Z_to_bv 64 4096)) with 4096.
    replace (bv_unsigned a <=? bv_unsigned a + 4096) with true by (symmetry; apply Z.leb_le; lia).
    replace (bv_unsigned a + 4096 + 4096 <=? bv_unsigned a + 8192) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity. }
  split; apply E.
Qed.

(* [comment removed for export] *)
Lemma mapped_le_of_acc : forall C U mo, acc C U mo -> U <= vm_limit (m_vmmaps mo) -> MrAccSpec.mapped mo <= vm_limit (m_vmmaps mo).
Proof. intros C U mo (_ & _ & _ & H & _) HU. lia. Qed.
