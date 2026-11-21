(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require MmapSim RefNodes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.MSafe. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. Import SM01.KStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KEv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM06. Import SM06. Import SM06.MI_Contracts.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require MM15. Import MM15. Import MM15.ProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrBridge MrNodes MrFeasSome MrKRefuse MrKGrant MrFeasLift MrFeasLift2 MrRoom MrAccSpec MrAcc MrAccNodes MrAccPath
  MrKGrant2 MrUcb MrGen.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition limok (lim : Z) (mo : Model) : Prop := lim <= vm_limit (m_vmmaps mo).

Lemma limok_mm : forall lim, mm_inv (limok lim).
Proof.
  intros lim n mo rsp mo' evs Hn Hst H. unfold limok in *. rewrite (lim_mm n mo rsp mo' evs); [exact H | | exact Hst].
  destruct n; try contradiction; exact I.
Qed.

Definition budget (lim : Z) (c u : Z) : Prop := c <= 40000 /\ u <= lim.

Lemma budget_down : forall lim c u c' u', budget lim c u -> c' <= c -> u' <= u -> budget lim c' u'.
Proof. intros lim c u c' u' [H1 H2] Hc Hu. split; lia. Qed.

Definition grants (e : ev) (z : Z) : Prop :=
  match e with
  | EBrk req => req = 0 \/ z <> req
  | EMmap _ _ _ _ => is_err z = false
  | EMprotect _ _ _ => z = 0
  | _ => False
  end.

Section Lift.
Context {rc : runConstT}.

Lemma ev_grant_none_path : forall L (G : PState -> Model -> Prop) s0 mo len,
  KL L (ps_brk s0) mo -> 0 < len < 2^63 ->
  (exists a : word, RefNodes.grant_ok_na (Z_to_bv 64 0) mo a (page_round_up_Z len) = true) ->
  exists z s' mo', tpath nstep (ev_step (ld_atop L) (EMmap 0 len PROT_NONE MAPF) s0) mo [] (Ok (z, s')) mo' /\ is_err z = false.
Proof.
  intros L G s0 mo len HK Hlen [a Hg].
  pose proof (nstep_mmap_none_grant len mo a Hlen Hg) as Hst. cbv zeta in Hst.
  destruct (RefNodes.grant_ok_na_unpack _ _ _ _ Hg) as (Hal & Hpos & Htop & _).
  assert (Hn0 : 0 <= page_round_up_Z len) by (apply page_round_up_Z_nonneg; lia).
  pose proof (alloc_top_lt64 (m_vmmaps mo)) as Hcl.
  exists (bv_unsigned a), s0, (with_vmmaps (none_next (m_vmmaps mo) a (Z_to_bv 64 (page_round_up_Z len))) mo). split.
  - unfold ev_step. change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false. cbv iota.
    change (PROT_NONE =? 0) with true. cbv iota.
    eapply (tpath_mbind_ok _ _ s0 mo (MmOk (bv_unsigned a)) s0).
    + apply (tpath_msys_ok _ _ s0 mo _ _ (MmOk (bv_unsigned a)) Hst).
      unfold dec_mmap_none, mmap_addr_ok, mmap_len. rewrite !bv_eqb_refl. cbn [andb].
      rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos). cbn [andb].
      rewrite (kl_atop _ _ _ HK). rewrite (proj2 (Z.leb_le _ _) Htop). reflexivity.
    + cbv beta iota. apply tpath_ret_ok.
  - unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Lemma ev_grant_mprotect_path : forall L (G : PState -> Model -> Prop) s0 mo a C U,
  KL L (ps_brk s0) mo -> event_pre L (EMprotect a PGSZ PROT_RW) -> acc C U mo -> U <= vm_limit (m_vmmaps mo) ->
  exists s' mo', tpath nstep (ev_step (ld_atop L) (EMprotect a PGSZ PROT_RW) s0) mo [] (Ok (0, s')) mo'.
Proof.
  intros L G s0 mo a0 C U HK Hpre HA HU.
  cbn [event_pre] in Hpre. destruct Hpre as (Hq & _ & _ & b & l & k & Hin & -> & Hk2).
  pose proof (KL_atop_lt _ _ _ HK) as HKat.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
  pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
  set (a := b + (1 + k) * PGSZ). set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *.
  set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
  assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
  assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
  { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
    rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hcm : map_contains (vm_maps h) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
    replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hrng : 0 < a < 2 ^ 63) by (unfold PGSZ in *; lia).
  (* the page misses the vDSO pair: it lies in a mapped entry, every mapped entry is
     free of the reserved ledger (kl_mres), and the pair is in that ledger (kl_vin). *)
  assert (Hvd : region_free (vdso_reserved (m_kernel mo) (vdso_top h)) aw nw = true).
  { apply region_free_sep. intros y Hy.
    pose proof (region_free_disj _ _ _ y (kl_mres _ _ _ HK _ A5) (kl_vin _ _ _ HK _ Hy)) as D.
    unfold elo, ehi in B5, B6, D |- *. rewrite Ua, Un. lia. }
  pose proof (nstep_mprotect_rw_grant a mo Hrng Hamod Hcn Hcm (mapped_le_of_acc C U mo HA HU) Hvd) as Hst.
  exists s0, (mprotect_model_next mo (Z_to_bv 64 a) (Z_to_bv 64 4096)).
  unfold ev_step.
  eapply tpath_mbind_ok; [apply (tpath_msys_ok _ _ s0 mo _ _ (RgDone true) Hst)|cbv beta iota; apply tpath_ret_ok].
  unfold dec_mprotect_rw, dec_mprotect. change (mmap_len PGSZ) with 4096.
  change (bv_unsigned (Z_to_bv 64 0) =? 0) with true. rewrite !bv_eqb_refl. reflexivity.
Qed.




End Lift.
