(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (NF_mmap_anon takes Linux's placement (mmap_place_found); 1 recorded proof replaced by written proofs (mmap_answer_ok_of_free); nstep_mmap_anon_err_forced, NF_mmap_anon restated for the revision's model; NF_mmap_anon proves the non-NORESERVE backing test from the budget (zstd/zstd_frame_info's text)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode NodesMm04.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Malloc KInv KStep PState KLink KEv Relim StepB EKPlace Gap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Placement.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_NFKern () := "I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2or00K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC59OSSVerify5KrLib3Lib6Decode8errno_ofC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC59OSSVerify5KrLib4Spec5KStep;mmap_len_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap?mmap_noaccess_bC59OSSVerify5KrLib3Lib9NodesMm04Mnstep_mmap_none_err_refusableC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic8eq_ind_rC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap>mmap_modeled_bC59OSSVerify5KrLib3Lib9NodesMm04Knstep_mmap_rw_err_refusableC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C47Corelib4Init5Logic9False_indC59OSSVerify5KrLib3Lib9PlacementDmmap_grant_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementFmmap_reserve_refusableC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib4Spec6Malloc9PROT_NONEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics?LinuxProcessSem5State6ENOMEMI4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec4KInv4MAPFC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5State8vm_limitC59OSSVerify5KrLib3Lib9Placement@vm_gap_availableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indc59OSSVerify5KrLib4Spec6NFKernJnstep_mmap_anon_err_forcedC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4Mmap@mmap_noreserve_bC59OSSVerify5KrLib4Spec5Relim?backing_le_liveC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?vm_backing_usedK46Stdlib9micromega7EnvRing5PExpr03C59OSSVerify5KrLib3Lib9NodesMm04Kgrant_refusable_false_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9NodesMm04Mreserve_refusable_false_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB2NFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State<map_containsC4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm4MmapEmmap_fixed_noaccess_bC59OSSVerify5KrLib3Lib9NodesMm04Lnstep_mmap_fixed_none_no_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv5MAPFXC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9NodesMm04Lnstep_mprotect_err_refusableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9PlacementBmprotect_refusableC1?~~~~~~~~~~~~~~~C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Mm8MprotectCmprotect_model_nextC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupC45stdpp9bitvector;definitions;bv_unsignedK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry02C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem5State=maps_subtractC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_start_brkC4ELinuxProcessSemantics?LinuxProcessSem5State6vm_brkC4ELinuxProcessSemantics?LinuxProcessSem5State<vm_mmap_baseK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01C4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC59OSSVerify5KrLib4Spec5RelimEm_vm_lazy_with_vmmapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5RelimMm_vm_materialized_with_vmmapsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesC4ELinuxProcessSemantics?LinuxProcessSem5StateDm_vmmaps_with_vmmapsC56Stdlib6ZArith6BinInt1Z8le_transC59OSSVerify5KrLib3Lib9NodesMm04Nmprotect_refusable_false_introC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC6ELinuxProcessSemantics?LinuxProcessSem3Sys6Kernel4Fork@PID_MAX_ENVELOPEI59OSSVerify5KrLib4Spec5KLink2KL00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_atopC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib4Spec5KLink:KL_atop_ltC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv?mmap_len_pos_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEvAregion_free_app_rC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv>went_In_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink4wentC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KStep>round_up_pg_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec3KEv@region_free_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink3eloC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink3ehiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5KLink9kl_brkregC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib4Spec5KLink4wcovC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C59OSSVerify5KrLib4Spec3KEv<wcov_rf_disjC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7lrangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=is_errno_formC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC59OSSVerify5KrLib4Spec6Malloc;iv_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3KEv:In_lrangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv7ld_resvC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib4Spec5KLink7kl_resvC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffC59OSSVerify5KrLib4Spec5KLink3wwZC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib3Lib6Decode>region_free_InC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC59OSSVerify5KrLib4Spec4KInv8ld_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec5KStepCround_up_pg_alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbC56Stdlib6ZArith6BinInt1Z6leb_leC47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool:orb_true_rC56Stdlib6ZArith6BinInt1Z8eqb_reflC56Stdlib6ZArith6BinInt1Z6ltb_ltC46Stdlib4Bool4Bool>orb_true_introC56Stdlib6ZArith6BinInt1Z6ltb_geC59OSSVerify5KrLib4Spec4KInv9ld_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4KInv9ld_brkregC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib4Init5Logic7f_equalK46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib4Spec4KInv7LEN_MAXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec4KInv4mled00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List8map_consI47Corelib4Init9Datatypes:comparison00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma nstep_mmap_anon_err_forced : forall len prot mo rsp mo' evs,
  0 < len -> mmap_len len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  nstep (NMmap 0 len prot MAPF) mo rsp mo' evs ->
  errno_of (eff_ret rsp) <> None ->
  (prot = PROT_RW /\ mmap_grant_refusable_at (Z_to_bv 64 MAPF) mo (Z_to_bv 64 0) (mmap_len len) = true)
  \/ (prot = PROT_NONE /\ mmap_reserve_refusable_at mo (Z_to_bv 64 0) (mmap_len len) = true).
Proof.
  intros len prot mo rsp mo' evs Hlen Hlen2 Hp H He. pose proof (mmap_len_ge len Hlen) as ML.
  destruct (errno_of (eff_ret rsp)) as [e|] eqn:E; [|congruence].
  destruct Hp as [-> | ->].
  - right. split; [reflexivity|].
    destruct (nstep_mmap_none_err_refusable 0 len PROT_NONE MAPF ltac:(lia) mo rsp mo' evs e eq_refl H E) as (_ & R & _). exact R.
  - left. split; [reflexivity|].
    destruct (nstep_mmap_rw_err_refusable 0 len PROT_RW MAPF ltac:(lia) mo rsp mo' evs e eq_refl H E) as (_ & R & _). exact R.
Qed.

(* [comment removed for export] *)
Lemma NF_mmap_anon : forall len prot mo,
  0 < len -> mmap_len len < 2^63 -> (prot = PROT_NONE \/ prot = PROT_RW) ->
  m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  vm_live_bytes (m_vmmaps mo) + mmap_len len <= vm_limit (m_vmmaps mo) ->
  (* LPS 75d69e00: the request is placed where Linux puts it; this is that it has a place. *)
  mmap_place_found mo (Z_to_bv 64 0) (mmap_len len) = true ->
  NF (NMmap 0 len prot MAPF) mo.
Proof.
  intros len prot mo Hlen Hlen2 Hp Hlz Hmt Hbud Hpf rsp mo' evs Hst.
  destruct (errno_of (eff_ret rsp)) eqn:E; [|reflexivity]. exfalso.
  destruct (nstep_mmap_anon_err_forced len prot mo rsp mo' evs Hlen Hlen2 Hp Hst ltac:(rewrite E; discriminate)) as [[_ R]|[_ R]].
  - rewrite (grant_refusable_at_false_intro (Z_to_bv 64 MAPF) mo (Z_to_bv 64 0) (mmap_len len)) in R; [discriminate| | exact Hpf].
    (* LPS 727298f3: a non-NORESERVE request is refusable when its backing exceeds the limit *)
    unfold mmap_noreserve_backed_ok. destruct (mmap_noreserve_b (Z_to_bv 64 MAPF)); [reflexivity|]. apply Z.leb_le.
    pose proof (backing_le_live mo Hlz Hmt). lia.
  - rewrite (reserve_refusable_at_false_intro mo (Z_to_bv 64 0) (mmap_len len) Hpf) in R. discriminate.
Qed.

(* [comment removed for export] *)
Lemma NF_mmap_fixed : forall a mo,
  let h := m_vmmaps mo in
  0 < a -> a + PGSZ <= alloc_top h -> a mod 4096 = 0 ->
  region_free (vm_reserved h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  NF (NMmap a PGSZ PROT_NONE MAPFX) mo.
Proof.
  intros a mo h Ha Hc Hal Hrf Hmc rsp mo' evs Hst. pose proof (alloc_top_lt h) as HT. unfold two_pow_64 in HT.
  assert (ML : mmap_len PGSZ = PGSZ) by reflexivity.
  destruct (nstep_mmap_fixed_none_no_err a PGSZ PROT_NONE MAPFX ltac:(unfold PGSZ; lia) ltac:(lia) Hal
              ltac:(rewrite ML; lia) mo rsp mo' evs eq_refl Hst) as (E & _ & _).
  exact E.
Qed.

(* [comment removed for export] *)
Lemma NF_mprotect : forall a mo,
  let h := m_vmmaps mo in
  0 <= a -> a + PGSZ < 2^64 -> a mod 4096 = 0 ->
  map_contains (vm_noaccess h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  map_contains (vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 PGSZ) = true ->
  vm_live_bytes h <= vm_limit h -> minv mo ->
  NF (NMprotect a PGSZ PROT_RW) mo.
Proof.
  intros a mo h Ha Hb Hal Hcn Hcm Hl Hmi rsp mo' evs Hst.
  assert (ML : mmap_len PGSZ = PGSZ) by reflexivity.
  destruct (errno_of (eff_ret rsp)) as [e|] eqn:E; [|reflexivity]. exfalso.
  destruct (nstep_mprotect_err_refusable a PGSZ ltac:(unfold PGSZ; lia) Ha Hal ltac:(rewrite ML; lia) mo rsp mo' evs e Hst E)
    as (_ & _ & _ & _ & _ & R).
  rewrite ML in R. rewrite (mprotect_refusable_false_intro a PGSZ mo) in R; [discriminate|].
  eapply Z.le_trans; [apply backing_le_live| ].
  - unfold mprotect_model_next. rewrite m_vm_lazy_with_vmmaps. apply Hmi.
  - unfold mprotect_model_next. rewrite m_vm_materialized_with_vmmaps. apply Hmi.
  - unfold mprotect_model_next. rewrite m_vmmaps_with_vmmaps. cbn [vm_limit]. unfold vm_live_bytes in *. cbn [vm_maps]. exact Hl.
Qed.

(* [comment removed for export] *)
Lemma mmap_answer_ok_of_free : forall L pbrk mo a len,
  KL L pbrk mo -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  0 < a -> a mod 4096 = 0 -> a + n <= ld_atop L ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  mmap_answer_ok (ld_atop L) (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo a len HK Hlen h n A2 A1 A3 Hrf. pose proof (KL_atop_lt _ _ _ HK) as Hcl.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split.
  - unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
    rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
    unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
    enough (a + n <= lo \/ lo + m <= a) as D.
    { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
    apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
    + apply (kl_resv_sub _ _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
      pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ua, Un in D. exact D.
    + injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
    + injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
    + injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
      rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia.
  - unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.
