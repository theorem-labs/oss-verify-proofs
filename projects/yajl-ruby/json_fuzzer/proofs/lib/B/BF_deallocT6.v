(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg ZBridge InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA MmStep StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed XB_mmap_fixed_srz.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanWf6 AsanWf7 AsanWf8 AsanWf9 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanRepX AsanFrame AsanRealloc AsanRefillMB AsanRepEnqB AsanRepRefillB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_qrepL BF_qrep B_iface BX_unreg BX_Exit BF_place BF_fakestack_rep BF_kit BF_kit2 BF_poison BF_free_kit BF_qkit BF_mmfix1 BF_unwind BF_gbb BF_free5 BF_free5s BF_free6 BF_free12 BF_ldealloc1 BF_ldealloc4 B_policy5 B_slack5 B_budget5 B_mmchk5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 B_bframe BF_alloc_iface BF_populate_iface BF_refill_iface BF_tkit BF_ainv_kit BF_statics BF_popdefs BF_pop0 BF_popT BF_caT BF_refill_room BF_refillT BF_ldcT BF_deallocT1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Model.
Variable E : aenv.
#[local] Notation SB := (ae_space_beg E).

(* [comment removed for export] *)
Definition rel_st (cb n : Z) (a : astate) : astate :=
  upd_dead (fun d => <[cb := n]> d) (upd_chunks (delete cb) (upd_ts (ts_on_real_free n) a)).

Lemma rel_as_regions : forall cb n a, as_regions (rel_st cb n a) = as_regions a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_cache : forall cb n a, as_cache (rel_st cb n a) = as_cache a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_cache_inited : forall cb n a, as_cache_inited (rel_st cb n a) = as_cache_inited a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_cache_stale : forall cb n a, as_cache_stale (rel_st cb n a) = as_cache_stale a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_cache_allocated : forall cb n a, as_cache_allocated (rel_st cb n a) = as_cache_allocated a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_cache_mapped : forall cb n a, as_cache_mapped (rel_st cb n a) = as_cache_mapped a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_tq : forall cb n a, as_tq (rel_st cb n a) = as_tq a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_gq : forall cb n a, as_gq (rel_st cb n a) = as_gq a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_sec : forall cb n a, as_sec (rel_st cb n a) = as_sec a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_ptr_committed : forall cb n a, as_ptr_committed (rel_st cb n a) = as_ptr_committed a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_sec_stats : forall cb n a, as_sec_stats (rel_st cb n a) = as_sec_stats a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_sec_stale : forall cb n a, as_sec_stale (rel_st cb n a) = as_sec_stale a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_glob_allocated : forall cb n a, as_glob_allocated (rel_st cb n a) = as_glob_allocated a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_glob_mapped : forall cb n a, as_glob_mapped (rel_st cb n a) = as_glob_mapped a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_oom : forall cb n a, as_oom (rel_st cb n a) = as_oom a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_nprim_ever : forall cb n a, as_nprim_ever (rel_st cb n a) = as_nprim_ever a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_residue : forall cb n a, as_residue (rel_st cb n a) = as_residue a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_everc : forall cb n a, as_everc (rel_st cb n a) = as_everc a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_ndepot_ins : forall cb n a, as_ndepot_ins (rel_st cb n a) = as_ndepot_ins a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_node_blocks : forall cb n a, as_node_blocks (rel_st cb n a) = as_node_blocks a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_store_blocks : forall cb n a, as_store_blocks (rel_st cb n a) = as_store_blocks a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_keys : forall cb n a, as_keys (rel_st cb n a) = as_keys a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_frames : forall cb n a, as_frames (rel_st cb n a) = as_frames a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_store_stored : forall cb n a, as_store_stored (rel_st cb n a) = as_store_stored a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_ia_inited : forall cb n a, as_ia_inited (rel_st cb n a) = as_ia_inited a. Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_chunks : forall cb n a, as_chunks (rel_st cb n a) = delete cb (as_chunks a). Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_as_ts : forall cb n a, as_ts (rel_st cb n a) = ts_on_real_free n (as_ts a). Proof. intros cb n a; destruct a; reflexivity. Qed.
Lemma rel_get_region : forall cb n a c, get_region (rel_st cb n a) c = get_region a c. Proof. intros cb n a c; destruct a; reflexivity. Qed.
Lemma rel_get_cache : forall cb n a c, get_cache (rel_st cb n a) c = get_cache a c. Proof. intros cb n a c; destruct a; reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_qcbr_prim : forall P D a cb cm c i j f orc res,
  AWf E P D a -> as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i j -> cm_prim cm = Some c ->
  arun f (local_dealloc E c (cm_alloc_beg cm) (rel_st cb (cm_n cm) a)) orc = Some res ->
  arun f (qcb_recycle E cb a) orc = Some res.
Proof.
  intros P D a cb cm c i j f orc res WF Hcm ST PC RUN.
  pose proof (prim_chunk_geometry E P D a cb cm c WF Hcm PC) as GEO. cbv zeta in GEO. destruct GEO as (IP & DIVc & MODc & BEG & MU & POS).
  pose proof (chunk_beg_loc E P D a cb cm WF Hcm) as CL. rewrite PC in CL. destruct CL as (Hc & CV & _).
  unfold qcb_recycle. eapply arun_bind_l; [apply arun_aget|]. rewrite Hcm, ST. cbv beta iota zeta. rewrite IP, MODc.
  unfold acheck at 1. replace (negb (c =? 0) && negb (c =? 31)) with true
    by (symmetry; apply andb_true_intro; unfold kLargestClassID in Hc; split; apply negb_true_iff, Z.eqb_neq; lia).
  eapply arun_bind_l.
  { eapply arun_bind_l; [apply arun_aret|]. rewrite ?DIVc, BEG. replace (_ <=? _) with true by (symmetry; apply Z.leb_le; exact MU). apply arun_aret. }
  destruct (carved_class_of_addr E a c (cm_alloc_beg cm) Hc (proj1 WF) (proj1 (proj2 WF)) CV) as [IPab CLS].
  rewrite IPab. eapply arun_bind_l.
  { unfold acheck. rewrite Z.eqb_refl. eapply arun_bind_l; [apply arun_aret|]. rewrite PC, CLS, Z.eqb_refl. apply arun_aret. }
  eapply arun_bind_l; [apply arun_aupd|].
  replace (cm_alloc_beg cm =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite ?IPab, CLS.
  eapply arun_bind_l; [apply arun_aupd|]. exact RUN.
Qed.

(* [comment removed for export] *)
Definition ldl_st (cb : Z) (cm : chunkmeta) (sc : secchunk) (i : nat) (a : astate) : astate :=
  let n := cm_n cm in let msz := sc_map_size sc in
  let a1 := upd_chunks (delete cb) (upd_ts (ts_on_real_free n) a) in
  let secl := as_sec a in let lastc := List.last secl sc in
  let a2 := upd_glob (fun x => x - msz) (fun x => x - msz)
              (upd_sec_stats (fun st => mkSecStats (ss_n_allocs st) (ss_n_frees st + 1) (ss_cur st - msz) (ss_max st) (ss_by_size_log st))
                (upd_sec_stale (fun st => <[Z.of_nat (Nat.pred (length secl)) := sc_map_beg lastc]> st)
                  (upd_sec (fun _ => removelast (list_set secl i lastc)) a1))) in
  upd_ts (ts_on_munmap msz) a2.
(* [comment removed for export] *)
Definition sec_orc (A L : Z) : list aans := [AnsOk 0].
Definition sec_evs (A L : Z) : list aev := [AEvMunmap A L].

Lemma run_qcbr_sec : forall P D a cb cm sc (i : nat) i0 j0 orc,
  AWf E P D a -> as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i0 j0 -> cm_prim cm = None ->
  nth_error (as_sec a) i = Some sc -> cm_alloc_beg cm = sc_map_beg sc + kPageSize ->
  exists f, arun f (qcb_recycle E cb a) (sec_orc (sc_map_beg sc) (sc_map_size sc) ++ orc)
            = Some (ldl_st cb cm sc i a, ONorm tt, sec_evs (sc_map_beg sc) (sc_map_size sc), orc).
Proof.
  intros P D a cb cm sc i i0 j0 orc WF Hcm ST PC NTH AB.
  destruct (sec_chunk_entry E P D a cb cm WF Hcm PC) as (sc' & Hsc' & Hab' & Hms & L1 & L2 & OUT & HBsc & NP).
  pose proof WF as X. destruct X as (WE & WR & WC & WCH & WQ & (S1 & S2 & S3 & S4 & S5) & WD).
  pose proof (nth_error_In _ _ NTH) as Hsc.
  assert (Esc : sc' = sc).
  { apply (NoDup_map_inj_In _ _ _ _ S4 Hsc' Hsc). rewrite AB in Hab'. unfold kPageSize in Hab'. lia. }
  subst sc'. clear Hab'.
  pose proof (sec_block_begin_ok E P D a cb cm WF Hcm PC) as SBB.
  assert (IPab : in_primary SB (cm_alloc_beg cm) = false).
  { unfold in_primary. rewrite AB. unfold kPageSize in L1 |- *. unfold kSpaceSize in OUT |- *.
    destruct OUT as [O|O]; [apply andb_false_intro1; apply Z.leb_gt; lia| apply andb_false_intro2; apply Z.ltb_ge; lia]. }
  unfold qcb_recycle.
  eexists ?[f].
  eapply arun_bind_l; [apply arun_aget|]. rewrite Hcm, ST. cbv beta iota zeta. rewrite NP.
  eapply arun_bind_l; [apply arun_aret|]. rewrite SBB, IPab.
  eapply arun_bind_l; [apply arun_aret|].
  eapply arun_bind_l; [apply arun_aupd|].
  replace (cm_alloc_beg cm =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite AB; unfold kPageSize; lia). rewrite ?IPab.
  unfold acheck. rewrite Z.eqb_refl. eapply arun_bind_l; [apply arun_aret|]. rewrite PC. eapply arun_bind_l; [apply arun_aret|].
  eapply arun_bind_l; [apply arun_aupd|].
  (* [comment removed for export] *)
  unfold large_dealloc. eapply arun_bind_l; [apply arun_aget|]. cbv beta zeta. cbn [as_sec upd_chunks upd_ts].
  replace (cm_alloc_beg cm - kPageSize) with (sc_map_beg sc) by (rewrite AB; lia).
  destruct (list_find_index (fun c => sc_map_beg c =? sc_map_beg sc) (as_sec a) 0) as [i'|] eqn:FI.
  2:{ exfalso. eapply (AsanWf8.list_find_index_some (fun c => sc_map_beg c =? sc_map_beg sc)); [exact Hsc| apply Z.eqb_refl| exact FI]. }
  destruct (AsanWf8.list_find_index_spec _ _ _ _ FI) as (x & _ & NTH' & FX). rewrite Nat.sub_0_r in NTH'.
  apply Z.eqb_eq in FX. pose proof (NoDup_map_inj_In _ _ _ _ S4 (nth_error_In _ _ NTH') Hsc FX) as Ex. subst x.
  assert (Ei : i' = i).
  { pose proof S4 as ND. clear -ND NTH NTH'. revert i i' NTH NTH' ND. generalize (as_sec a). intros l.
    induction l as [|y l IH]; intros i i' NTH NTH' ND; [destruct i; discriminate|].
    cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
    destruct i as [|i]; destruct i' as [|i']; cbn in NTH, NTH'; [reflexivity| | |].
    - exfalso. injection NTH as ->. apply NI. apply in_map. exact (nth_error_In _ _ NTH').
    - exfalso. injection NTH' as ->. apply NI. apply in_map. exact (nth_error_In _ _ NTH).
    - f_equal. exact (IH i i' NTH NTH' ND'). }
  subst i'. rewrite NTH'.
  eapply arun_bind_l; [apply arun_aupd|].
  unfold sec_orc, sec_evs.
  assert (MUN : forall s1 o, arun 1%nat ((aupd (upd_ts (ts_on_munmap (sc_map_size sc)));;; call_munmap (sc_map_beg sc) (sc_map_size sc)) s1) (AnsOk 0 :: o)
                       = Some (upd_ts (ts_on_munmap (sc_map_size sc)) s1, ONorm tt, [AEvMunmap (sc_map_beg sc) (sc_map_size sc)], o)).
  { intros s1 o. unfold call_munmap. cbn -[upd_ts ts_on_munmap Z.eqb]. rewrite Z.eqb_refl. reflexivity. }
  unfold poison_zero. cbn [app]. replace [AEvMunmap (sc_map_beg sc) (sc_map_size sc)] with ([] ++ [AEvMunmap (sc_map_beg sc) (sc_map_size sc)]) by reflexivity.
  eapply (arun_abind _ _ _ 1%nat 1%nat); [reflexivity|]. rewrite MUN. reflexivity.
Qed.

End Model.

(* [comment removed for export] *)
Definition K_ITEM : Z := 688.     (* [comment removed for export] *)

Section DeallocT6.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation RI := (ae_region_info E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation INST := 0xaaf58.
#[local] Notation CA := (ae_thread E0 + kThrCache).
#[local] Notation PP := (BF_caT.PP E0 FSB0 HR0).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FPW5a (lo cb ab g l8 : Z) (z : Z) : Prop :=
     lo <= z \/ (cb <= z < cb + 4) \/ (ab <= z < ab + 8)
  \/ (kShadowBase + g <= z < kShadowBase + g + l8)
  \/ (T + kThrStats + 40 <= z < T + kThrStats + 56).
Definition R5a_stmt : Prop :=
  forall (a : astate) (m m' : mem) (lo cb c i j g : Z) (D : list batch) (cm : chunkmeta),
  let n := cm_n cm in let ab := cm_alloc_beg cm in let l8 := (n + 7) / 8 in
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i j -> cm_prim cm = Some c -> 8 * g = cb + 16 ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AsanRepEnqB.renv_ok E0 a ->
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPW5a lo cb ab g l8 z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (kShadowBase + g) [CB (Z.to_nat l8) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat l8))] ->
  rw_cells bsegs m' (T + kThrStats + 40) [C8 (wz (ts_real_frees (as_ts a) + 1)); C8 (wz (ts_really_freed (as_ts a) + n))] ->
  ARep bsegs E0 (DepotR bsegs E0) (rel_st cb n a) m'.
(* [comment removed for export] *)
Definition R5a : R5a_stmt := BF_qrepL.R5a_holds E0.

(* [comment removed for export] *)
Definition FPW7 (a : astate) (lo : Z) (sc : secchunk) (i : nat) (z : Z) : Prop :=
  let A := sc_map_beg sc in let L := sc_map_size sc in let lastc := List.last (as_sec a) sc in
     lo <= z
  \/ (ae_instance E0 + kInsNReserved + 8 <= z < ae_instance E0 + kInsNReserved + 17)
  \/ (ae_instance E0 + kInsSecStats + 8 <= z < ae_instance E0 + kInsSecStats + 24)
  \/ (ae_instance E0 + kInsSecMutex <= z < ae_instance E0 + kInsSecMutex + 4)
  \/ (ae_instance E0 + kInsGlobalStats + 16 <= z < ae_instance E0 + kInsGlobalStats + 32)
  \/ (ae_ptr_array E0 + 8 * Z.of_nat i <= z < ae_ptr_array E0 + 8 * Z.of_nat i + 8)
  \/ (sc_map_beg lastc + 24 <= z < sc_map_beg lastc + 32)
  \/ (T + kThrStats + 40 <= z < T + kThrStats + 56) \/ (T + kThrStats + 88 <= z < T + kThrStats + 104)
  \/ (kShadowBase + A / 8 <= z < kShadowBase + A / 8 + L / 8)
  \/ (A <= z < A + L).
Definition R7_stmt : Prop :=
  forall (a : astate) (m m' : mem) (lo cb i0 j0 : Z) (i : nat) (D : list batch) (cm : chunkmeta) (sc : secchunk) (junk : list word),
  let n := cm_n cm in let A := sc_map_beg sc in let L := sc_map_size sc in let lastc := List.last (as_sec a) sc in
  let a' := ldl_st cb cm sc i a in let st := as_sec_stats a in let ts := as_ts a in
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i0 j0 -> cm_prim cm = None ->
  nth_error (as_sec a) i = Some sc -> cm_alloc_beg cm = A + kPageSize ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AsanRepEnqB.renv_ok E0 a ->
  (forall z, 0 <= z < 2^64 -> ~ FPW7 a lo sc i z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (ae_instance E0 + kInsNReserved) [C8 (wz (as_ptr_committed a)); C8 (wz (n_chunks a - 1)); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsSecStats) [C8 (wz (ss_n_allocs st)); C8 (wz (ss_n_frees st + 1)); C8 (wz (ss_cur st - L)); C8 (wz (ss_max st))] ->
  rw_cells bsegs m' (ae_instance E0 + kInsSecMutex) [C4 (wz 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsGlobalStats + 16) [C8 (wz (as_glob_allocated a - L)); C8 (wz (as_glob_mapped a - L))] ->
  u64arr bsegs m' (ae_ptr_array E0) (map (fun c => wz (sc_map_beg c)) (as_sec a') ++ junk) -> (length (as_sec a') + length junk = Z.to_nat kChunksBlockCount)%nat ->
  (sc_map_beg lastc <> A -> rw_cells bsegs m' (sc_map_beg lastc + 24) [C8 (wz (Z.of_nat i))]) ->
  rw_cells bsegs m' (T + kThrStats + 40) [C8 (wz (ts_real_frees ts + 1)); C8 (wz (ts_really_freed ts + n))] ->
  rw_cells bsegs m' (T + kThrStats + 88) [C8 (wz (ts_munmaps ts + 1)); C8 (wz (ts_munmaped ts + L))] ->
  rw_cells bsegs m' (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (L / 8)))] ->
  ARep bsegs E0 (DepotR bsegs E0) a' m'.
(* [comment removed for export] *)
Lemma IC0_T6 : ae_ic E0 = both_ic.
Proof. pose proof ENV0 as X. destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IC0 & _). exact IC0. Qed.
Definition R7 : R7_stmt := BF_qrep.R7_holds E0 IC0_T6.
Definition R5b : BF_ldcT.R5b_stmt E0 := BF_qrepL.R5b_holds E0.
Definition R6 : BF_ldcT.R6_stmt E0 := BF_qrepL.R6_holds E0.
#[local] Notation LDC := (ldc_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok ENV0 PL0OK L0OK R5b R6).


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma live_blocks_del_quar : forall (a a' : astate) cb cm i j,
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i j -> as_chunks a' = delete cb (as_chunks a) ->
  Permutation (live_blocks a') (live_blocks a).
Proof.
  intros a a' cb cm i j Hcm ST E. unfold live_blocks, chunk_list. rewrite E.
  pose proof (map_to_list_delete (as_chunks a) cb cm Hcm) as P1.
  symmetry. etransitivity. { apply Permutation_map. apply Permutation_filterb. symmetry. exact P1. }
  cbn [List.filter map snd]. rewrite ST. reflexivity.
Qed.

(* [comment removed for export] *)
Definition last_beg (a : astate) : Z := match rev (as_sec a) with [] => 0 | c :: _ => sc_map_beg c end.

(* [comment removed for export] *)
Definition item_W (a : astate) (cb : Z) (cm : chunkmeta) (usp : Z) : list (Z * Z) :=
  let n := cm_n cm in let ab := cm_alloc_beg cm in
  [ (usp - K_ITEM, usp); (T + kThrStats + 40, T + kThrStats + 56) ]
  ++ match cm_prim cm with
     | Some c => [ (cb, cb + 4); (ab, ab + 8); (kShadowBase + (cb + 16) / 8, kShadowBase + (cb + 16) / 8 + (n + 7) / 8) ] ++ ldc_W E0 a c usp
     | None => let A := ab - kPageSize in let L := map_size n in
               [ (0xaaf58 + kInsNReserved + 8, 0xaaf58 + kInsNReserved + 17); (0xaaf58 + kInsSecStats + 8, 0xaaf58 + kInsSecStats + 24);
                 (0xaaf58 + kInsSecMutex, 0xaaf58 + kInsSecMutex + 4); (0xaaf58 + kInsGlobalStats + 16, 0xaaf58 + kInsGlobalStats + 32);
                 (ae_ptr_array E0, ae_ptr_array E0 + 8 * kChunksBlockCount); (last_beg a + 24, last_beg a + 32);
                 (T + kThrStats + 88, T + kThrStats + 104); (kShadowBase + A / 8, kShadowBase + A / 8 + L / 8); (A, A + L) ]
     end.

(* [comment removed for export] *)
Definition item_sameC (a a' : astate) (cb : Z) : Prop :=
     as_chunks a' = delete cb (as_chunks a) /\ as_tq a' = as_tq a /\ as_gq a' = as_gq a /\ as_ptr_committed a' = as_ptr_committed a
  /\ as_nprim_ever a' = as_nprim_ever a /\ as_residue a' = as_residue a /\ as_everc a' = as_everc a
  /\ as_ndepot_ins a' = as_ndepot_ins a /\ as_node_blocks a' = as_node_blocks a /\ as_store_blocks a' = as_store_blocks a
  /\ as_keys a' = as_keys a /\ as_frames a' = as_frames a /\ as_store_stored a' = as_store_stored a
  /\ as_cache_inited a' = true /\ as_cache_mapped a' = as_cache_mapped a /\ as_ia_inited a' = as_ia_inited a /\ as_oom a' = as_oom a
  /\ (forall c, rg_mapped_user (get_region a' c) = rg_mapped_user (get_region a c) /\ rg_alloc_user (get_region a' c) = rg_alloc_user (get_region a c))
  /\ (forall c, rg_mapped_fa (get_region a c) <= rg_mapped_fa (get_region a' c))
  /\ regions_bytes a <= regions_bytes a' <= regions_bytes a + kFreeArrayMapSize
  /\ Permutation (live_blocks a') (live_blocks a).
Definition item_sameP (a a' : astate) : Prop :=
  as_sec a' = as_sec a /\ as_sec_stats a' = as_sec_stats a /\ as_sec_stale a' = as_sec_stale a /\ as_glob_allocated a' = as_glob_allocated a /\ as_glob_mapped a' = as_glob_mapped a.
Definition item_sameS (a a' : astate) (cm : chunkmeta) : Prop :=
  exists sc, In sc (as_sec a) /\ cm_alloc_beg cm = sc_map_beg sc + kPageSize /\ sc_map_size sc = map_size (cm_n cm)
  /\ Permutation (sc :: as_sec a') (as_sec a)
  /\ ss_cur (as_sec_stats a') = ss_cur (as_sec_stats a) - sc_map_size sc /\ ss_max (as_sec_stats a') = ss_max (as_sec_stats a)
  /\ (forall c, get_region a' c = get_region a c).
Definition item_same (a a' : astate) (cb : Z) (cm : chunkmeta) : Prop :=
  item_sameC a a' cb /\ match cm_prim cm with Some _ => item_sameP a a' | None => item_sameS a a' cm end.

Definition item_post (D : list batch) (a a' : astate) (cb : Z) (cm : chunkmeta) (m m' : mem) (mo mo' : Model) (s : aps) (C C' lo usp : Z) : Prop :=
     (exists fuel orc evs orc', arun fuel (qcb_recycle E0 cb a) orc = Some (a', ONorm tt, evs, orc'))
  /\ ARep bsegs E0 (DepotR bsegs E0) a' m' /\ AWf E0 [] D a' /\ AKern E0 a' mo' /\ RTOKc C C' (sA a' s) mo'
  /\ m_fs mo' = m_fs mo /\ m_fds mo' = m_fds mo /\ m_tid mo' = m_tid mo
  /\ stk bsegs m' lo usp /\ mem_inv bsegs m' /\ rt_misc5 FSB0 PL0 E0 m' /\ munch (item_W a cb cm usp) m m'
  /\ item_same a a' cb cm.

(* [comment removed for export] *)
Theorem qitem_prim_srz :
  forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 stackp : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (D : list batch) (cm : chunkmeta) (cb c i j CBP lo usp C C' : Z) (K : TSet),
  let a := aps_alloc s in
  K [] ->
  RTOKc C C' s mo -> ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AKern E0 a mo -> res_ok a ->
  mem_inv bsegs m -> rt_misc5 FSB0 PL0 E0 m ->
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i j -> cm_prim cm = Some c ->
  (forall b, In b (as_tq a ++ as_gq a) -> ~ In cb (b_items b)) ->
  kFreeArrayMapSize <= gapR a -> rg_mapped_fa (get_region a c) + kFreeArrayMapSize <= kFreeArraySize ->
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_ITEM -> usp mod 16 = 0 -> usp < 2^47 -> tp = wz 0x5e1550 ->
  usp <= CBP -> CBP + 16 < 2^47 -> rw_cells bsegs m CBP [C8 (wz CA); C8 stackp] ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     item_post D a a' cb cm m m' mo mo' s C C' lo usp ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz CBP) (wz cb) a2 a3 a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz 0x34c64) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros until K. cbv zeta. intros KN TOK REP WF AK RES MI RT Hcm ST PC NIB RR RFA SK LOC LO SPA SPH TP HCB1 HCB2 CBC KONT.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  set (a := aps_alloc s) in *.
  unfold K_ITEM in LO. assert (USPR : 0 <= usp < 2^64) by (clear -LO LOC CR SPH; lia).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & GLE). fold a in GR0, GD0, GLE.
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (D0a & D0b & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  (* [comment removed for export] *)
  pose proof REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Rins as (I1 & I2 & _).
  pose proof (pop_statics_of E0 FSB0 PL0 a m IC0 REP RT) as PST. pose proof PST as [STA PG].
  unfold ae_instance in I1, I2. rewrite IC0 in I1, I2. cbn [aic_instance both_ic kInsSpaceBeg kInsSecondary Z.add] in I1, I2.
  pose proof WF as (WE & WR & WC & WK & WQ & WS & WD). pose proof WC as (WC1 & WC2 & WC3). pose proof WK as [WK1 WK2].
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 & WE19 & WE20 &
                    WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & _).
  unfold app_mem in WE14, WE16. rewrite KHB, KLE in WE14, WE16.
  assert (HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling).
  { rewrite KHB in WE2. split; [clear -WE2 WE3; lia|]. split; [clear -WE1; Z.div_mod_to_equations; nia| clear -WE4 WE5; unfold kSpaceSize in WE4 |- *; lia]. }
  assert (HSBH : kHighMemBeg <= SB) by (clear -WE2 WE3; lia).
  assert (HSBH8 : kHighMemBeg + 8 <= SB) by (rewrite KHB; rewrite KHB in WE2; clear -WE1 WE2 WE3; Z.div_mod_to_equations; lia).
  assert (HRI : RI = SB + kSpaceSize) by reflexivity.
  (* [comment removed for export] *)
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & CT & DT & CD & [IA1 IA2]).
  pose proof TR as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ RT) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  assert (TC : thread_cells m tp 0x6028f8 CTX T).
  { pose proof FSE as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
    split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
    rewrite TP. rewrite unsigned_lit by (clear; lia). exact FTSD. }
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
  pose proof CR0 as (_ & _ & _ & CRS & _). pose proof DR0 as (_ & _ & _ & DRS & _). change kResvLen with 137439023104 in CRS, DRS.
  unfold app_mem in WE25. rewrite ?KHB, ?KLE in WE25. unfold kIArenaLen in WE25, WE26, WE27, IA2.
  pose proof WE as WEx. destruct WEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE35x).
  unfold img_sep, kIArenaLen in WE35x. rewrite EI1 in WE35x.
  assert (PLC : placed_s CTX 4096).
  { apply placed_placed_s. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG. clear -IA1 IA2 WE25 WE26 WE35x EI2. lia. }
  assert (HTSB : T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) by (unfold kSpaceSize; clear -WE19 G1 G3; lia).
  assert (HCSB : CTX + 4096 <= SB \/ SB + kSpaceSize + 4096 <= CTX) by (unfold kSpaceSize; clear -WE27 IA1 IA2 G1 G3; lia).
  (* [comment removed for export] *)
  destruct (WK1 _ _ Hcm) as (ECB & KNr & ERZ & KP & KS). rewrite PC in KP. destruct KP as (FP & Ec & CV & NFc & NCc & NBc). rewrite ST in KS. destruct KS as (I1p & J1p & _).
  pose proof (chunk_beg_loc E0 [] D a cb cm WF Hcm) as CL. rewrite PC in CL. destruct CL as (HC & _ & ABle & CB8).
  pose proof HC as HC30. unfold kLargestClassID in HC30. pose proof (proj2 (class_size_mod c HC30)) as CS. set (size := class_size c) in *.
  pose proof (chunk_user_in_block E0 [] D a cb cm WF Hcm) as (U1 & U2 & U3). unfold user_lo, user_hi, blk_lo, blk_hi in U1, U2, U3. rewrite PC in U2. fold size in U2.
  pose proof (prim_chunk_geometry E0 [] D a cb cm c WF Hcm PC) as GEO. cbv zeta in GEO. destruct GEO as (IPcb & DIVc & MODc & BEG & MUle & ABpos).
  set (n := cm_n cm) in *. set (ab := cm_alloc_beg cm) in *.
  assert (UB : cm_user_beg cm = cb + 16) by (unfold kChunkHeaderSize in U3; clear -U3; lia).
  assert (RZ0 : 0 <= cm_rz_log cm) by (rewrite ERZ; unfold rz_log; clear; repeat (destruct (_ <=? _)); lia).
  assert (UBR : ab + 16 * 2 ^ cm_rz_log cm = cb + 16) by (rewrite <- UB; reflexivity).
  assert (HMAG : ab <> cb -> 16 < 16 * 2 ^ cm_rz_log cm).
  { intros NE. assert (P1 : 2 ^ 0 <= 2 ^ cm_rz_log cm) by (apply Z.pow_le_mono_r; clear -RZ0; lia). change (2 ^ 0) with 1 in P1.
    assert (P2 : 2 ^ cm_rz_log cm <> 1) by (intros E1; apply NE; rewrite E1 in UBR; clear -UBR; lia). clear -P1 P2. nia. }
  destruct (proj2 WR c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12). cbv zeta in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12.
  unfold region_of in A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12. set (r := get_region a c) in *.
  pose proof CV as (kp & K0 & KE & KB). unfold region_of in KB. fold r size in KE, KB.
  assert (HAB : ab = SB + c * 2^32 + (cb - SB) mod 2^32 / size * size /\ ab <= cb).
  { split; [| exact ABle]. rewrite <- BEG. unfold region_beg, kRegionSize. change (2^32) with 4294967296. fold size. clear. lia. }
  set (idx := (cb - SB) mod 2^32 / size) in *.
  set (mu := rg_mapped_user r).
  assert (HMU : (idx + 1) * size <= mu /\ 0 <= mu <= 0xE0000000) by (subst mu idx; unfold kRegionSize in MUle; fold size in MUle; unfold kFreeArrayOffset in A3; clear -MUle A1 A3; split; [exact MUle| lia]).
  assert (HCB : SB <= cb /\ cb + 24 <= SB + kSpaceSize /\ cb mod 16 = 0).
  { pose proof (chunk_user_aligned E0 [] D a cb cm WF Hcm) as UA. unfold user_lo in UA. rewrite UB in UA.
    unfold region_beg, kRegionSize in KE. unfold kFreeArrayOffset in A3. unfold kSpaceSize. clear -KE KB K0 A1 A3 CS HC30 ABle U2 UB KNr UA. subst n.
    split; [nia|]. split; [nia| Z.div_mod_to_equations; lia]. }
  assert (HN : cb + 16 + n <= SB + kSpaceSize).
  { rewrite <- UB. unfold region_beg, kRegionSize in KE. unfold kFreeArrayOffset in A3. unfold kSpaceSize. clear -KE KB K0 A1 A3 CS HC30 U2. nia. }
  set (nhi := n / 2^32). set (nlo := n mod 2^32).
  assert (HNHI : 0 <= nhi < 256) by (subst nhi; clear -KNr; subst n; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (HNLO : 0 <= nlo < 2^32) by (subst nlo; clear; apply Z.mod_pos_bound; lia).
  assert (En : n = nhi * 2^32 + nlo) by (subst nhi nlo; clear -KNr; rewrite Z.mul_comm; apply Z_div_mod_eq_full).
  set (g := (cb + 16) / 8). assert (Hg8 : 8 * g = cb + 16) by (subst g; clear -HCB; Z.div_mod_to_equations; lia).
  set (l8 := (n + 7) / 8).
  (* [comment removed for export] *)
  destruct (Rch _ _ Hcm) as [_ ((b1 & HB1x & HDRb) & MAGc & _)]. rewrite ST in HDRb. cbn [hdr_state hdr_alloc_id] in HDRb. rewrite <- ECB in HDRb. fold n in HDRb.
  set (b1' := b1 mod 256). assert (HB1 : 0 <= b1' < 256) by (subst b1'; clear; apply Z.mod_pos_bound; lia).
  assert (HDR : rw_cells bsegs m cb [C4 (wz (3 + 256 * (b1' + 256 * nhi))); C4 (wz nlo); C8 (wz i)]).
  { rewrite En in HDRb. fold nhi in HDRb.
    replace (Z_to_bv 8 b1) with (Z_to_bv 8 b1') in HDRb by (subst b1'; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite Z.mod_mod by (clear; lia); reflexivity).
    generalize HDRb. clear -HNHI HNLO HB1. intros HDRb.
    eapply BF_free_kit.rw_cells_reshape; [| | exact HDRb]; [cbn; tauto|].
    cbn [cells_bytes cbytes map app]. unfold le4, le2, le1. rewrite !Z_to_bv_unsigned. cbn [Z_to_le_bytes map app].
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64).
    unfold kChunkQuarantine. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite ?app_nil_r.
    rewrite !(Z.mod_small _ (2^64)) by lia.
    repeat (apply f_equal2; [Z.div_mod_to_equations; lia|]). reflexivity. }
  assert (MAG : ab <> cb -> rw_cells bsegs m ab [C8 (wz kAllocBegMagicVal); C8 (wz cb)]).
  { intros NE. pose proof (MAGc (HMAG NE)) as X. rewrite <- ECB in X. exact X. }
  assert (RIM : rw_cells bsegs m (RI + 128 * c + 48) [C8 (wz mu)]).
  { pose proof (Rri c ltac:(unfold kNumClasses; clear -HC30; lia)) as X. unfold region_of in X. fold r in X. unfold region_cells in X.
    pose proof (BF_kit3.rwc_split bsegs m _ [C8 (AsanRep.zw 0); C4 (AsanRep.zw 0); C4 (AsanRep.zw 0); C8 (AsanRep.zw (rg_num_freed r)); C8 (AsanRep.zw (rg_mapped_fa r)); C8 (AsanRep.zw (rg_alloc_user r)); C8 (AsanRep.zw 0)] _ X) as [_ Y].
    pose proof (BF_kit3.rwc_split bsegs m _ [C8 (AsanRep.zw (rg_mapped_user r))] _ Y) as [Z0 _].
    cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in Z0. unfold kRegSize in Z0. replace (RI + 128 * c + 48) with (RI + 128 * c + 48) by reflexivity.
    subst mu. replace (RI + 128 * c + 48) with (RI + 128 * c + 48)%Z by reflexivity. exact Z0. }
  (* [comment removed for export] *)
  assert (L8F : BF_free5.l8 nhi nlo = l8) by (unfold BF_free5.l8, BF_free5.n; subst l8; rewrite <- En; reflexivity).
  assert (L8P : 0 < l8 /\ 8 * l8 < n + 8 /\ n <= 8 * l8) by (subst l8; clear -KNr; subst n; Z.div_mod_to_equations; lia).
  assert (SH : rw_cells bsegs m (0x7fff8000 + g) [CB (Z.to_nat (BF_free5.l8 nhi nlo)) (repeat (Z_to_bv 8 kAsanHeapFreeMagic) (Z.to_nat (BF_free5.l8 nhi nlo)))]).
  { rewrite L8F. change 0x7fff8000 with kShadowBase. apply (BF_tkit.shadow_join m kShadowBase g (Z.to_nat l8) kAsanHeapFreeMagic); [| clear -L8P; lia].
    intros g' Hg'. apply (Rsh g' kAsanHeapFreeMagic). rewrite Z2Nat.id in Hg' by (clear -L8P; lia).
    rewrite (block_Sh E0 [] D a cb cm (8 * g') WF Hcm).
    - unfold chunk_shadow. rewrite ST. fold n. rewrite UB. unfold round_up.
      replace (8 * g' <? cb + 16) with false by (symmetry; apply Z.ltb_ge; clear -Hg' Hg8; lia).
      replace (8 * g' <? cb + 16 + (n + 8 - 1) / 8 * 8) with true by (symmetry; apply Z.ltb_lt; subst l8; clear -Hg' Hg8 L8P; Z.div_mod_to_equations; lia). reflexivity.
    - unfold blk_lo, blk_hi. rewrite PC. fold ab size. subst l8.
      pose proof (chunk_user_aligned E0 [] D a cb cm WF Hcm) as UA. unfold user_lo in UA. rewrite UB in UA.
      clear -Hg' Hg8 U1 U2 UB KNr UA CS K0 KE HCB. subst n. unfold region_beg, kRegionSize in KE. Z.div_mod_to_equations. nia. }
  (* [comment removed for export] *)
  set (rf := ts_real_frees (as_ts a) mod 2^64). set (rfd := ts_really_freed (as_ts a) mod 2^64).
  assert (TST : rw_cells bsegs m (T + 2840) [C8 (wz rf); C8 (wz rfd)]).
  { pose proof (BF_tkit.u64arr_cell m _ _ 5 _ Tst eq_refl) as X5. pose proof (BF_tkit.u64arr_cell m _ _ 6 _ Tst eq_refl) as X6.
    pose proof (BF_kit3.rwc_join_at bsegs m _ _ _ _ X5 X6 ltac:(cbn; clear; lia)) as X. cbn [app] in X. unfold kThrStats in X.
    replace (T + 2800 + 8 * Z.of_nat 5) with (T + 2840) in X by (clear; lia). subst rf rfd. rewrite !BF_popT.wz_mod. exact X. }
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI)] [C1 (Z_to_bv 8 0)] I1) as [INS4 _].
  (* [comment removed for export] *)
  set (P0 := PP s mo).
  pose proof (BF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo R0 R0' ATK) as KIP0.
  assert (AKs : AKern E0 (aps_alloc s) mo) by exact AK.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo AKs WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PCBP : forall y k, CBP <= y -> y + Z.of_nat k <= CBP + 16 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo AKs WE ENV0); clear -H1 H2 LOC LO HCB1 HCB2 CR; lia. }
  assert (PDAT : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 s mo AKs WE ENV ENV0); clear -H1 H2; lia. }
  assert (PRO : forall y k, 0x10000 <= y -> y + Z.of_nat k <= 0x31000 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 s mo AKs WE ENV ENV0); clear -H1 H2; lia. }
  assert (PT : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_thread' E0 FSB0 HR0 s mo AKs WE); assumption. }
  assert (PRIR : forall y k, RI + 128 * c <= y -> y + Z.of_nat k <= RI + 128 * c + 128 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite HRI in H1, H2. unfold P0, BF_caT.PP. apply (pol_reginfo' E0 FSB0 HR0 s mo WE); change kSpaceSize with (2^37) in H1, H2; clear -H1 H2 HC30; lia. }
  assert (PBLK : forall y k, ab <= y -> y + Z.of_nat k <= ab + size -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. destruct k as [|k']; [apply acc_ok_empty|]. unfold P0, BF_caT.PP.
    apply (pol_user E0 FSB0 HR0 s mo [] D AKs WF c y (Datatypes.S k') HC); [| | clear; lia]; fold a r; subst ab; clear -H1 H2 KE KB K0 A1 CS; nia. }
  assert (BL32 : cb + 32 <= ab + size).
  { pose proof (proj1 (class_size_mod c HC30)) as CSM. fold size in CSM. clear -U2 UB UBR KNr CSM CS RZ0. subst n ab.
    pose proof (Z.pow_pos_nonneg 2 (cm_rz_log cm) ltac:(lia) RZ0) as PP0. set (P2 := 2 ^ cm_rz_log cm) in *. Z.div_mod_to_equations. lia. }
  assert (PCH : forall y k, cb <= y -> y + Z.of_nat k <= cb + 24 -> P0 (Z_to_bv 64 y, k)) by (intros y k H1 H2; apply PBLK; [clear -H1 ABle; lia| clear -H2 BL32; lia]).
  assert (PAB : forall y k, ab <= y -> y + Z.of_nat k <= ab + 16 -> P0 (Z_to_bv 64 y, k)) by (intros y k H1 H2; apply PBLK; [exact H1| clear -H2 CS; lia]).
  assert (PSH : forall y k, 0x7fff8000 + g <= y -> y + Z.of_nat k <= 0x7fff8000 + g + BF_free5.l8 nhi nlo -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. rewrite L8F in H2. unfold P0, BF_caT.PP. apply (pol_space_shadow' E0 FSB0 HR0 s mo WE); rewrite A_SB_val; change kSpaceSize with (2^37);
      unfold kSpaceSize in HN, HCB, HSB; clear -H1 H2 Hg8 L8P HCB HN HSB; Z.div_mod_to_equations; lia. }
  assert (PCTX : P0 (Z_to_bv 64 (CTX + 152), 8%nat)).
  { unfold P0, BF_caT.PP. apply (pol_resv_range' E0 FSB0 HR0 s mo AKs c0 cl _ _ CR0); clear -CC1 CC2; cbn; lia. }
  (* [comment removed for export] *)
  set (a1 := rel_st cb n a).
  set (Q1 := fun ms' : machine_state => exists (m1 : mem) (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ms' = MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 (wz CA) (wz INST) (wz c) (wz ab) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x35068) fc None m1 (seg_rom bsegs)
        /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
        /\ munch [(usp + -112, usp); (cb, cb + 4); (ab, ab + 8); (0x7fff8000 + g, 0x7fff8000 + g + l8); (T + 2840, T + 2856)] m m1 /\ wmono bsegs m m1
        /\ rw_cells bsegs m1 (0x7fff8000 + g) [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfa) (Z.to_nat l8))]
        /\ rw_cells bsegs m1 (T + 2840) [C8 (wz (rf + 1)); C8 (wz (n + rfd))]).
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P0 Q1).
  { eapply (qcbr_prim_walk P0 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Q1 usp lo CBP cb SB RI c idx mu ab b1' nhi nlo (wz i) (wz CA) stackp
              LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) SPA HSB HRI HCB (conj HC ltac:(subst idx; change (2^32) with kRegionSize; exact DIVc)) eq_refl HMU HAB HB1 HNHI HNLO
              PSTK PDAT PRO PCH PAB PRIR HSBH8 ltac:(fold n; unfold BF_free5.n; rewrite <- En; exact HN)
              m g (wz cb) _ 0x6028f8 CTX T rf rfd Hg8 MI SK INS4 RIM);
      [ unfold BF_free5.hk; exact HDR | exact MAG | exact SH | exact PG | exact CBC | exact HCB1 | clear -HCB2; lia | exact TC | clear; lia | clear; lia | exact PLC | exact TR2
      | rewrite TP, unsigned_lit by (clear; lia); clear; lia | exact CT | exact HTSB | exact HCSB | exact TST
      | subst rf; apply Z.mod_pos_bound; clear; lia | subst rfd; apply Z.mod_pos_bound; clear; lia | exact PSH | exact PCTX | exact PT | exact PCBP |].
    intros m1 t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' MI1 SK1 MU1 WM1 INS1 RIM1 HDR1 MAG1 SH1 PG1 CBC1 TC1 TST1.
    apply evtA_done. unfold Q1. exists m1, t0', t1', t2', a4', a5', a6', a7', t3', t4', t5', t6'.
    rewrite L8F in MU1, SH1. unfold BF_free5.n in TST1. rewrite <- En in TST1.
    repeat match goal with |- _ /\ _ => split end; first [reflexivity| assumption]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1. unfold Q1 in HQ1.
  destruct HQ1 as (m1 & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MI1 & SK1 & MU1 & WM1 & SH1 & TST1).
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _). destruct KIP1 as [KIA1 _].
  assert (AGW : forall z, 0 <= z < 2^64 -> ~ FPW5a lo cb ab g l8 z -> m1 (wa z) = m (wa z)).
  { intros z Hz NF. apply MU1. rewrite wa_unsigned by exact Hz. unfold FPW5a, kThrStats, kShadowBase in NF. cbn [outside]. clear -NF LO Hz. repeat split; try exact I; lia. }
  pose proof (renv_of E0 PL0 ENV0 PL0OK D a mo WF AK EI1 EI2) as RENV.
  assert (REP1 : ARep bsegs E0 (DepotR bsegs E0) a1 m1).
  { apply (R5a a m m1 lo cb c i j g D cm Hcm ST PC Hg8 REP WF RENV WM1 AGW LOC).
    - unfold kShadowBase. fold n l8. change kAsanHeapLeftRedzoneMagic with 250. exact SH1.
    - unfold kThrStats. fold n. replace (T + 2800 + 40) with (T + 2840) by (clear; lia). subst rf rfd.
      rewrite !BF_popT.wz_mod_add in TST1. rewrite (Z.add_comm n) in TST1. rewrite BF_popT.wz_mod_add in TST1. exact TST1. }
  (* [comment removed for export] *)
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1.
  assert (TOK1' : RTOKc C C' (sA a1 s) mo1).
  { apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a a1 mo1).
    - change a with (aps_alloc s). rewrite BF_popT.sA_self. exact TOK1.
    - subst a1. unfold same_fp. rewrite rel_as_sec, rel_as_ptr_committed, rel_as_residue, rel_as_node_blocks, rel_as_store_blocks.
      rewrite (regions_bytes_same a (rel_st cb n a) (rel_get_region cb n a)). repeat split; reflexivity.
    - apply rel_as_nprim_ever. - apply rel_as_ndepot_ins. }
  assert (AK1 : AKern E0 a1 mo1).
  { apply (AKern_ext E0 a a1); [apply rel_as_regions| apply rel_as_ptr_committed| apply rel_as_sec| apply rel_as_node_blocks| apply rel_as_store_blocks|].
    exact (AKern_frame _ _ _ _ Fvm1 Flz1 AK). }
  assert (WF1 : AWf E0 [] D a1).
  { subst a1. unfold rel_st. apply (AWf_delete_chunk E0 [] D); [| cbn [as_tq as_gq upd_ts]; exact NIB]. eapply AWf_same_core; [apply same_core_upd_ts| exact WF]. }
  assert (AV1 : avail E0 D a1 c ab).
  { subst a1 ab. unfold rel_st. apply (deleted_block_avail E0 [] D _ cb cm c); [| exact Hcm| exact PC]. eapply AWf_same_core; [apply same_core_upd_ts| exact WF]. }
  assert (CI1 : as_cache_inited a1 = true).
  { subst a1. rewrite rel_as_cache_inited. destruct (as_cache_inited a) eqn:CI0; [reflexivity| exfalso].
    destruct (WC2 eq_refl) as [_ RE]. clear -KB K0 CS RE. subst r. unfold get_region in KB. rewrite RE, lookup_empty in KB. cbn in KB. nia. }
  assert (RES1 : res_ok a1) by (subst a1; unfold res_ok; rewrite rel_as_sec, rel_as_residue; exact RES).
  assert (ABlo : SB + c * 4294967296 <= ab) by (generalize KE K0 CS; clear; unfold region_beg, kRegionSize; intros; nia).
  assert (RT1 : rt_misc5 FSB0 PL0 E0 m1).
  { apply (rt_misc5_agree E0 FSB0 PL0 m m1 RT). intros z Hz.
    destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
    - apply MU1. rewrite wa_unsigned by (clear -ZI; lia). cbn [outside]. unfold kSpaceSize in HCB, HN. clear -ZI LOC LO CR Timg Tlo HCB HN HSB ABle ABlo HC30 Hg8 L8P. repeat split; try exact I; lia.
    - unfold rt_high2 in RH. apply MU1. rewrite wa_unsigned by (clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia). cbn [outside].
      unfold kSpaceSize in HCB, HN, HSB.
      (* [comment removed for export] *)
      destruct RH as [[RH|RH]|[RH|RH]];
        [ clear -RH LOC LO CR Tlo Thi Tband WE19 G1 G3 HSB HCB HN ABle ABlo HC30 Hg8 L8P
        | clear -RH LOC LO CR Tlo Thi Tband WE19 G1 G3 HSB HCB HN ABle ABlo HC30 Hg8 L8P
        | clear -RH LOC LO CR CT CQ2 CQ4 CC1 CC2 CRS G1 G3 HSB HCB HN ABle ABlo HC30 Hg8 L8P
        | clear -RH LOC LO CR DT DQ2 DQ4 DD1 DD2 DRS G1 G3 HSB HCB HN ABle ABlo HC30 Hg8 L8P ];
        repeat split; try exact I; lia. }
  assert (RR1 : kFreeArrayMapSize <= gapR a1) by (subst a1; rewrite (gapR_eq a (rel_st cb n a) (rel_as_nprim_ever cb n a) (regions_bytes_same a _ (rel_get_region cb n a))); exact RR).
  assert (RFA1 : rg_mapped_fa (get_region a1 c) + kFreeArrayMapSize <= kFreeArraySize) by (subst a1; rewrite rel_get_region; exact RFA).
  (* [comment removed for export] *)
  eapply (LDC ra gp tp t0' t1' t2' s0 s1 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 mo1 (sA a1 s) D c ab lo usp C C' K KN TOK1');
    cbn [aps_alloc sA aps_set_alloc]; [exact REP1| exact WF1| exact AK1| exact RES1| exact MI1| exact RT1| exact HC| exact AV1| exact CI1| exact RR1| exact RFA1| exact SK1| exact LOC| unfold K_LDC; clear -LO; lia
    | exact SPA| exact SPH| exact TP|].
  intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x m' mo' a' POST.
  destruct POST as (RUN' & REP' & WF' & AK' & TOK' & Ffs' & Ffds' & Ftid' & SK' & MI' & RT' & WM' & MU' & SAME').
  eapply KONT. unfold item_post.
  split. { destruct RUN' as (f & orc & evs & orc' & RUN'). exists f, orc, evs, orc'. apply (run_qcbr_prim E0 [] D a cb cm c i j f orc _ WF Hcm ST PC). exact RUN'. }
  split; [exact REP'|]. split; [exact WF'|]. split; [exact AK'|].
  split; [rewrite BF_popT.sA_sA in TOK'; exact TOK'|].
  split; [rewrite Ffs'; exact Ffs1|]. split; [rewrite Ffds'; exact Ffds1|]. split; [rewrite Ftid'; exact Ftid1|].
  split; [exact SK'|]. split; [exact MI'|]. split; [exact RT'|].
  split. { unfold item_W. rewrite PC. fold n ab. eapply munch_trans.
           - eapply munch_cover; [exact MU1|]. unfold K_ITEM, kShadowBase, kThrStats. subst g l8. clear -LO Hg8. solve_covers.
           - replace (ldc_W E0 a c usp) with (ldc_W E0 a1 c usp) by (unfold ldc_W; subst a1; rewrite rel_get_region; reflexivity).
             eapply munch_cover; [exact MU'|]. rewrite app_assoc. apply BF_qkit.covers_self_r. }
  unfold item_same. rewrite PC. unfold item_sameC, item_sameP. subst a1. unfold ldc_same in SAME'.
  destruct SAME' as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27 & X28).
  assert (PLB : Permutation (live_blocks a') (live_blocks a)).
  { apply (live_blocks_del_quar a a' cb cm i j Hcm ST). rewrite X1, rel_as_chunks. reflexivity. }
  rewrite X1, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, X16, X17, X18, X19, X21, X22, X23, X28.
  rewrite rel_as_chunks, rel_as_tq, rel_as_gq, rel_as_sec, rel_as_ptr_committed, rel_as_sec_stats, rel_as_sec_stale, rel_as_glob_allocated, rel_as_glob_mapped,
          rel_as_nprim_ever, rel_as_residue, rel_as_everc, rel_as_ndepot_ins, rel_as_node_blocks, rel_as_store_blocks, rel_as_keys, rel_as_frames, rel_as_store_stored,
          rel_as_cache_mapped, rel_as_ia_inited, rel_as_oom.
  rewrite !rel_get_region in X25, X26, X27 |- *. rewrite (regions_bytes_same a (rel_st cb n a) (rel_get_region cb n a)).
  repeat match goal with |- _ /\ _ => split end; try reflexivity; try exact X20; try exact PLB.
  - intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [split; [exact X25| exact X26]|]. destruct (X24 c' NE) as [GR _]. rewrite GR, rel_get_region. split; reflexivity.
  - intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [clear -X27; lia|]. destruct (X24 c' NE) as [GR _]. rewrite GR, rel_get_region. clear; lia.
  - clear -X27. unfold kFreeArrayMapSize in *. lia.
  - clear -X27. unfold kFreeArrayMapSize in *. lia.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shadow_join_any : forall m K lo k,
  (forall g, lo <= g < lo + Z.of_nat k -> exists v, rw_cells bsegs m (K + g) [C1 v]) -> (0 < k)%nat ->
  exists bs, rw_cells bsegs m (K + lo) [CB k bs].
Proof.
  intros m K lo k H Hk. revert lo H. induction k as [|k IH]; intros lo H; [lia|].
  destruct k as [|k'].
  - destruct (H lo ltac:(lia)) as [v X]. exists [v]. eapply (InitMem.rw_cells_recast bsegs); [exact X| cbn; auto| reflexivity| reflexivity].
  - destruct (H lo ltac:(lia)) as [v X]. destruct (IH ltac:(lia) (lo + 1)%Z ltac:(intros g Hg; apply H; lia)) as [bs Y].
    pose proof (proj1 (proj1 (proj1 Y))) as LY0. assert (LY : length bs = Datatypes.S k') by (cbn in LY0; first [exact (proj1 LY0) | exact LY0]). clear LY0.
    pose proof (BF_kit3.rwc_join_at bsegs m (K + lo) (K + (lo + 1)) [C1 v] _ X Y ltac:(cbn; lia)) as Z0.
    exists (v :: bs). eapply (InitMem.rw_cells_recast bsegs); [exact Z0| cbn; auto| reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma ld_statics_of : forall a m cnr, ae_ic E0 = both_ic ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> rt_misc5 FSB0 PL0 E0 m -> rw_cells bsegs m 0x601590 [C8 cnr] ->
  ld_statics m cnr.
Proof.
  intros a m cnr IC0 Hrep Hrt CNR.
  pose proof (pop_statics_of E0 FSB0 PL0 a m IC0 Hrep Hrt) as [STA PG].
  destruct Hrt as (_ & [t XS] & _ & AMS & _).
  assert (US : unreg_statics m) by (unfold exit_statics in XS; decompose [and] XS; assumption).
  unreg_statics_open US.
  destruct AMS as (_ & _ & _ & GPAIR & MML & _ & _ & PGSZ & F244 & _ & _ & _ & GOTG).
  destruct Hrep as (_ & _ & _ & _ & _ & _ & _ & _ & Rglob & _).
  pose proof Rglob as (_ & _ & _ & Gdd & _ & Ghe & _ & _ & _ & Gps & Gdy & _).
  rewrite IC0 in Gdd, Ghe, Gps, Gdy. cbn [aic_common_flags aic_page_size_cached aic_dying_flag aic_kHighMemEnd both_ic Z.add] in Gdd, Ghe, Gps, Gdy.
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (AsanRep.zw kHighMemEnd)] [C8 (AsanRep.zw 0); C8 (AsanRep.zw 0)] Ghe) as [GHE1 GHE23]. cbn [cells_size csize Z.add Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in GHE23.
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (AsanRep.zw 0)] [C8 (AsanRep.zw 0)] GHE23) as [GHE2 GHE3]. cbn [cells_size csize Z.add Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in GHE3.
  split; [exact PG|]. split; [exact STA|]. split; [| split].
  - unfold BF_premap1.rsmr_statics. split; [exact GOTG|]. split; [exact CNR|]. split; [exact PGSZ|]. split; [exact F244| exact Gdd].
  - unfold BF_ldealloc2.flush_statics. split; [exact GSBP|]. split; [exact GSB|]. split; [exact GMB|]. split; [exact GHE2|]. split; [exact GME|]. split; [exact GHE3|].
    split; [exact GHE|]. split; [exact GHE1|]. split; [exact GPSC|]. split; [exact Gps| exact GPAIR].
  - unfold BF_ldealloc3.umd_statics. split; [exact GCF|]. split; [exact MML|]. split; [exact GPAIR| exact Gdy].
Qed.

(* [comment removed for export] *)
Lemma last_map_gen : forall {X Y} (f : X -> Y) (l : list X) d, List.last (map f l) (f d) = f (List.last l d).
Proof. intros X Y f l. induction l as [|x l IH]; intros d; [reflexivity|]. cbn [map]. destruct l as [|y l]; [reflexivity|]. cbn [List.last map] in IH |- *. apply IH. Qed.

Lemma swap_words : forall (l : list secchunk) (junk : list word) (i : nat) sc,
  nth_error l i = Some sc ->
  upd (map (fun c => wz (sc_map_beg c)) l ++ junk) i (wz (sc_map_beg (List.last l sc)))
  = map (fun c => wz (sc_map_beg c)) (removelast (list_set l i (List.last l sc))) ++ (wz (sc_map_beg (List.last l sc)) :: junk).
Proof.
  intros l junk i sc H. destruct (nth_error_split l i sc H) as (l1 & l2 & -> & <-).
  set (f := fun c : secchunk => wz (sc_map_beg c)).
  assert (CASES : l2 = [] \/ exists l2' z, l2 = l2' ++ [z]).
  { destruct l2 as [|u v]; [left; reflexivity| right]. destruct (exists_last (l := u :: v) ltac:(discriminate)) as (l2' & z & EQ). exists l2', z. exact EQ. }
  destruct CASES as [->|(l2' & z & ->)].
  - rewrite (List.last_last l1 sc sc). rewrite AsanWf8.list_set_app, AsanWf8.removelast_app_single. rewrite map_app. cbn [map].
    rewrite <- app_assoc. cbn [app]. replace (length l1) with (length (map f l1)) by apply length_map.
    exact (BF_popT.upd_app_mid (map f l1) junk (f sc) (f sc)).
  - replace (l1 ++ sc :: l2' ++ [z]) with ((l1 ++ sc :: l2') ++ [z]) by (rewrite <- app_assoc; reflexivity).
    rewrite (List.last_last (l1 ++ sc :: l2') z sc). rewrite <- app_assoc. cbn [app]. rewrite AsanWf8.list_set_app.
    replace (l1 ++ z :: l2' ++ [z]) with ((l1 ++ z :: l2') ++ [z]) by (rewrite <- app_assoc; reflexivity).
    rewrite AsanWf8.removelast_app_single. rewrite !map_app. cbn [map]. rewrite map_app. cbn [map]. rewrite <- !app_assoc. cbn [app].
    replace (length l1) with (length (map f l1)) by apply length_map.
    rewrite <- (app_assoc (map f l2') [f z] junk). cbn [app]. exact (BF_popT.upd_app_mid (map f l1) (map f l2' ++ f z :: junk) (f sc) (f z)).
Qed.

(* [comment removed for export] *)
Lemma ldl_as_regions : forall cb cm sc i a, as_regions (ldl_st cb cm sc i a) = as_regions a. Proof. reflexivity. Qed.
Lemma ldl_get_region : forall cb cm sc i a c, get_region (ldl_st cb cm sc i a) c = get_region a c. Proof. reflexivity. Qed.
Lemma ldl_get_cache : forall cb cm sc i a c, get_cache (ldl_st cb cm sc i a) c = get_cache a c. Proof. reflexivity. Qed.
Lemma ldl_as_cache_inited : forall cb cm sc i a, as_cache_inited (ldl_st cb cm sc i a) = as_cache_inited a. Proof. reflexivity. Qed.
Lemma ldl_as_cache_mapped : forall cb cm sc i a, as_cache_mapped (ldl_st cb cm sc i a) = as_cache_mapped a. Proof. reflexivity. Qed.
Lemma ldl_as_tq : forall cb cm sc i a, as_tq (ldl_st cb cm sc i a) = as_tq a. Proof. reflexivity. Qed.
Lemma ldl_as_gq : forall cb cm sc i a, as_gq (ldl_st cb cm sc i a) = as_gq a. Proof. reflexivity. Qed.
Lemma ldl_as_ptr_committed : forall cb cm sc i a, as_ptr_committed (ldl_st cb cm sc i a) = as_ptr_committed a. Proof. reflexivity. Qed.
Lemma ldl_as_oom : forall cb cm sc i a, as_oom (ldl_st cb cm sc i a) = as_oom a. Proof. reflexivity. Qed.
Lemma ldl_as_nprim_ever : forall cb cm sc i a, as_nprim_ever (ldl_st cb cm sc i a) = as_nprim_ever a. Proof. reflexivity. Qed.
Lemma ldl_as_residue : forall cb cm sc i a, as_residue (ldl_st cb cm sc i a) = as_residue a. Proof. reflexivity. Qed.
Lemma ldl_as_everc : forall cb cm sc i a, as_everc (ldl_st cb cm sc i a) = as_everc a. Proof. reflexivity. Qed.
Lemma ldl_as_ndepot_ins : forall cb cm sc i a, as_ndepot_ins (ldl_st cb cm sc i a) = as_ndepot_ins a. Proof. reflexivity. Qed.
Lemma ldl_as_node_blocks : forall cb cm sc i a, as_node_blocks (ldl_st cb cm sc i a) = as_node_blocks a. Proof. reflexivity. Qed.
Lemma ldl_as_store_blocks : forall cb cm sc i a, as_store_blocks (ldl_st cb cm sc i a) = as_store_blocks a. Proof. reflexivity. Qed.
Lemma ldl_as_keys : forall cb cm sc i a, as_keys (ldl_st cb cm sc i a) = as_keys a. Proof. reflexivity. Qed.
Lemma ldl_as_frames : forall cb cm sc i a, as_frames (ldl_st cb cm sc i a) = as_frames a. Proof. reflexivity. Qed.
Lemma ldl_as_store_stored : forall cb cm sc i a, as_store_stored (ldl_st cb cm sc i a) = as_store_stored a. Proof. reflexivity. Qed.
Lemma ldl_as_ia_inited : forall cb cm sc i a, as_ia_inited (ldl_st cb cm sc i a) = as_ia_inited a. Proof. reflexivity. Qed.
Lemma ldl_as_chunks : forall cb cm sc i a, as_chunks (ldl_st cb cm sc i a) = delete cb (as_chunks a). Proof. reflexivity. Qed.
Lemma ldl_as_sec : forall cb cm sc i a, as_sec (ldl_st cb cm sc i a) = removelast (list_set (as_sec a) i (List.last (as_sec a) sc)). Proof. reflexivity. Qed.
Lemma ldl_as_glob_allocated : forall cb cm sc i a, as_glob_allocated (ldl_st cb cm sc i a) = as_glob_allocated a - sc_map_size sc. Proof. reflexivity. Qed.
Lemma ldl_as_glob_mapped : forall cb cm sc i a, as_glob_mapped (ldl_st cb cm sc i a) = as_glob_mapped a - sc_map_size sc. Proof. reflexivity. Qed.
Lemma ldl_ss_cur : forall cb cm sc i a, ss_cur (as_sec_stats (ldl_st cb cm sc i a)) = ss_cur (as_sec_stats a) - sc_map_size sc. Proof. reflexivity. Qed.
Lemma ldl_ss_max : forall cb cm sc i a, ss_max (as_sec_stats (ldl_st cb cm sc i a)) = ss_max (as_sec_stats a). Proof. reflexivity. Qed.
Lemma regions_bytes_ldl : forall cb cm sc i a, regions_bytes (ldl_st cb cm sc i a) = regions_bytes a.
Proof. intros. apply regions_bytes_same. intros c. apply ldl_get_region. Qed.

(* [comment removed for export] *)
Lemma list_setn_upd : forall {X} (l : list X) i x, BF_ldealloc1.list_setn l i x = upd l i x.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x; cbn; [reflexivity| reflexivity| reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma nth_error_firstn_lt : forall {X} n (l : list X) i, (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X n. induction n as [|n IH]; intros l i Hi; [lia|]. destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|].
  cbn. apply IH. lia.
Qed.
Lemma last_nth : forall {X} (l : list X) d, l <> [] -> nth_error l (Nat.pred (length l)) = Some (List.last l d).
Proof.
  intros X l d NE. destruct (exists_last NE) as (l' & x & ->). rewrite length_app. cbn [length]. rewrite Nat.add_1_r. cbn [Nat.pred].
  rewrite (List.last_last l' x d). rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma last_In : forall {X} (l : list X) d, l <> [] -> In (List.last l d) l.
Proof. intros X l d NE. exact (nth_error_In _ _ (last_nth l d NE)). Qed.
Lemma length_list_set : forall {X} (l : list X) i x, length (list_set l i x) = length l.
Proof. intros X l. induction l as [|y l IH]; intros [|i] x; cbn; [reflexivity| reflexivity| reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem qitem_sec_srz :
  forall (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 stackp : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (mo : Model) (s : aps) (D : list batch) (cm : chunkmeta) (cb i j CBP lo usp C C' : Z) (K : TSet),
  let a := aps_alloc s in
  K [] ->
  RTOKc C C' s mo -> ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AKern E0 a mo -> res_ok a ->
  mem_inv bsegs m -> rt_misc5 FSB0 PL0 E0 m ->
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i j -> cm_prim cm = None ->
  (forall b, In b (as_tq a ++ as_gq a) -> ~ In cb (b_items b)) ->
  (forall sc, In sc (as_sec a) -> 0x603000 <= sc_map_beg sc) -> as_cache_inited a = true ->
  stk bsegs m lo usp -> alloc_ceiling <= lo -> lo <= usp - K_ITEM -> usp mod 16 = 0 -> usp < 2^47 -> tp = wz 0x5e1550 ->
  usp <= CBP -> CBP + 16 < 2^47 -> rw_cells bsegs m CBP [C8 (wz CA); C8 stackp] ->
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate),
     item_post D a a' cb cm m m' mo mo' s C C' lo usp ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra (wz usp) gp tp t0 t1 t2 s0 s1 (wz CBP) (wz cb) a2 a3 a4 a5 a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz 0x34c64) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros until K. cbv zeta. intros KN TOK REP WF AK RES MI RT Hcm ST PC NIB SECHI CI SK LOC LO SPA SPH TP HCB1 HCB2 CBC KONT.
  pose proof alloc_ceiling_range as CR. pose proof B_bundle.kHighMemBeg_val as KHB. pose proof kLowAppEnd_val as KLE.
  set (a := aps_alloc s) in *.
  unfold K_ITEM in LO. assert (USPR : 0 <= usp < 2^64) by (clear -LO LOC CR SPH; lia).
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HCR & HCR' & GR0 & GD0 & GLE). fold a in GR0, GD0, GLE.
  assert (ENV : ENVOK E0 FSB0 s) by exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK).
  pose proof ENV as ENV'. destruct ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EE & EFS & [EI1 EI2]). rewrite EE in EI1, EI2.
  pose proof ENV0 as ENV0'. destruct ENV0' as (D0a & D0b & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _ & _ & _ & _ & _ & IC0 & TDN & DNP).
  (* [comment removed for export] *)
  pose proof REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Rins as (I1 & I2 & _).
  pose proof (pop_statics_of E0 FSB0 PL0 a m IC0 REP RT) as PST. pose proof PST as [STA PG].
  unfold ae_instance in I1, I2. rewrite IC0 in I1, I2. cbn [aic_instance both_ic kInsSpaceBeg kInsSecondary Z.add] in I1, I2.
  pose proof WF as (WE & WR & WC & WK & WQ & WS & WD). pose proof WC as (WC1 & WC2 & WC3). pose proof WK as [WK1 WK2].
  pose proof WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 & WE19 & WE20 &
                    WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & _).
  unfold app_mem in WE14, WE16. rewrite KHB, KLE in WE14, WE16.
  assert (HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling).
  { rewrite KHB in WE2. split; [clear -WE2 WE3; lia|]. split; [clear -WE1; Z.div_mod_to_equations; nia| clear -WE4 WE5; unfold kSpaceSize in WE4 |- *; lia]. }
  assert (HSBH : kHighMemBeg <= SB) by (clear -WE2 WE3; lia).
  assert (HSBH8 : kHighMemBeg + 8 <= SB) by (rewrite KHB; rewrite KHB in WE2; clear -WE1 WE2 WE3; Z.div_mod_to_equations; lia).
  assert (HRI : RI = SB + kSpaceSize) by reflexivity.
  (* [comment removed for export] *)
  pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TR & CT & DT & CD & [IA1 IA2]).
  pose proof TR as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
  pose proof (rt_misc5_fsenv _ _ _ _ RT) as FSE.
  assert (T8 : T mod 8 = 0) by (unfold FSEnv in FSE; decompose [and] FSE; assumption).
  assert (TC : thread_cells m tp 0x6028f8 CTX T).
  { pose proof FSE as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
    split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
    rewrite TP. rewrite unsigned_lit by (clear; lia). exact FTSD. }
  pose proof (ak_resv_geom _ _ _ AK) as (G1 & G2 & G3). change kSpaceSize with 137438953472 in G3. change kPageSize with 4096 in G3. change kResvLen with 137439023104 in G3.
  pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
  pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
  pose proof CR0 as (_ & _ & _ & CRS & _). pose proof DR0 as (_ & _ & _ & DRS & _). change kResvLen with 137439023104 in CRS, DRS.
  unfold app_mem in WE25. rewrite ?KHB, ?KLE in WE25. unfold kIArenaLen in WE25, WE26, WE27, IA2.
  pose proof WE as WEx. destruct WEx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE35x).
  unfold img_sep, kIArenaLen in WE35x. rewrite EI1 in WE35x.
  assert (PLC : placed_s CTX 4096).
  { apply placed_placed_s. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG. clear -IA1 IA2 WE25 WE26 WE35x EI2. lia. }
  assert (HTSB : T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) by (unfold kSpaceSize; clear -WE19 G1 G3; lia).
  assert (HCSB : CTX + 4096 <= SB \/ SB + kSpaceSize + 4096 <= CTX) by (unfold kSpaceSize; clear -WE27 IA1 IA2 G1 G3; lia).
  (* [comment removed for export] *)
  destruct (WK1 _ _ Hcm) as (ECB & KNr & ERZ & KP & KS). rewrite PC in KP. destruct KP as [FP _]. rewrite ST in KS. destruct KS as (I1p & J1p & _).
  destruct (sec_chunk_entry E0 [] D a cb cm WF Hcm PC) as (sc & Hsc & Hab & Hms & L1 & L2 & OUT & HBsc & NP).
  pose proof WS as (S1 & S2 & S3 & S4 & S5).
  destruct (S3 sc Hsc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7). change kPageSize with 4096 in M1, M5, Hab, L1.
  set (n := cm_n cm) in *. set (A := sc_map_beg sc) in *. set (L := sc_map_size sc) in *.
  pose proof (SECHI sc Hsc) as AHI. fold A in AHI.
  pose proof (chunk_user_in_block E0 [] D a cb cm WF Hcm) as (U1 & U2 & U3). unfold user_lo, user_hi, blk_lo, blk_hi, kChunkHeaderSize in U1, U2, U3. rewrite PC in U2.
  change kPageSize with 4096 in U2. rewrite Hab, Hms in U2 || rewrite Hab in U2. fold n A L in U1, U2.
  assert (UB : cm_user_beg cm = cb + 16) by (clear -U3; lia).
  assert (CBHI : cb + 16 + n <= A + L) by (rewrite <- UB; clear -U2 Hms; subst L; rewrite Hms; lia).
  destruct (In_nth_error _ _ Hsc) as [ix NTH].
  (* [comment removed for export] *)
  set (cs := map (fun c => (sc_map_beg c, sc_map_size c)) (as_sec a)).
  assert (NTHcs : nth_error cs ix = Some (A, L)) by (subst cs A L; rewrite nth_error_map, NTH; reflexivity).
  assert (CSA : forall j c', nth_error cs j = Some c' -> exists sc', In sc' (as_sec a) /\ fst c' = sc_map_beg sc' /\ snd c' = sc_map_size sc').
  { intros jx c' Hj. subst cs. rewrite nth_error_map in Hj. destruct (nth_error (as_sec a) jx) as [sc'|] eqn:Ej; [| discriminate]. injection Hj as <-.
    exists sc'. split; [exact (nth_error_In _ _ Ej)| split; reflexivity]. }
  assert (LENcs : length cs = length (as_sec a)) by (subst cs; apply length_map).
  destruct Rsec as [[[P0 SEC0]|(PTRC & junk & PARRm & PLEN)] HDRSm]; [exfalso; rewrite SEC0 in Hsc; exact Hsc|].
  assert (LENCS : (Z.of_nat (length cs) + Z.of_nat (length junk) = kChunksBlockCount)%Z) by (rewrite LENcs; unfold kChunksBlockCount in PLEN |- *; clear -PLEN; lia).
  assert (RNG : Forall (fun c => 0x603000 <= fst c /\ fst c mod 4096 = 0 /\ 4096 <= snd c /\ fst c + snd c <= alloc_ceiling) cs).
  { apply Forall_forall. intros c' Hc'. subst cs. apply in_map_iff in Hc'. destruct Hc' as (sc' & <- & Hsc'). cbn [fst snd].
    destruct (S3 sc' Hsc') as (Q1 & Q2 & Q3 & Q4 & Q5 & _). change kPageSize with 4096 in Q1, Q5. pose proof (SECHI sc' Hsc') as Q6.
    clear -Q1 Q3 Q4 Q5 Q6. split; [exact Q6|]. split; [exact Q1|]. split; [Z.div_mod_to_equations; lia| exact Q3]. }
  assert (DISJ : forall j1 j2 cj ck, nth_error cs j1 = Some cj -> nth_error cs j2 = Some ck -> j1 <> j2 -> fst cj + snd cj <= fst ck \/ fst ck + snd ck <= fst cj).
  { intros j1 j2 cj ck H1 H2 NE. subst cs. rewrite nth_error_map in H1, H2.
    destruct (nth_error (as_sec a) j1) as [x1|] eqn:E1; [| discriminate]. destruct (nth_error (as_sec a) j2) as [x2|] eqn:E2; [| discriminate].
    injection H1 as <-. injection H2 as <-. cbn [fst snd]. apply (S5 x1 x2 (nth_error_In _ _ E1) (nth_error_In _ _ E2)).
    intros ->. apply NE. clear -E1 E2 S4. revert j1 j2 E1 E2 S4. generalize (as_sec a). intros l. induction l as [|y l IH]; intros j1 j2 E1 E2 ND; [destruct j1; discriminate|].
    cbn [map] in ND. inversion ND as [|? ? NI ND']; subst. destruct j1 as [|j1]; destruct j2 as [|j2]; cbn in E1, E2; [reflexivity| | |].
    - exfalso. injection E1 as ->. apply NI. apply in_map. exact (nth_error_In _ _ E2).
    - exfalso. injection E2 as ->. apply NI. apply in_map. exact (nth_error_In _ _ E1).
    - f_equal. exact (IH j1 j2 E1 E2 ND'). }
  (* [comment removed for export] *)
  pose proof (ptr_placed E0 FSB0 s WE ENV) as PAP. unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kPtrArrayLen in PAP. destruct PAP as (PA0 & PA1 & PA2).
  set (PA := ae_ptr_array E0) in *.
  pose proof (chunk_user_aligned E0 [] D a cb cm WF Hcm) as UA. unfold user_lo in UA. rewrite UB in UA.
  assert (HCB : 0x603000 <= cb /\ cb + 16 <= alloc_ceiling /\ cb mod 16 = 0) by (clear -L1 CBHI M3 AHI UA KNr; subst n; split; [lia| split; [lia| Z.div_mod_to_equations; lia]]).
  assert (HCBS : cb + 16 <= SB \/ SB + kSpaceSize <= cb) by (clear -OUT L1 CBHI KNr; subst n; lia).
  assert (HPA : 0x603000 <= PA /\ PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= alloc_ceiling) by (rewrite LENCS; unfold kChunksBlockCount; clear -PA0 PA1; lia).
  assert (HBB : A + 4096 = gbb_result cs cb).
  { symmetry. apply (gbb_result_hit cs ix A L cb NTHcs); [clear -L1 L2; lia| | exact DISJ].
    apply Forall_forall. intros c' Hc'. pose proof (proj1 (Forall_forall _ _) RNG c' Hc') as (Q1 & _ & Q3 & _). clear -Q1 Q3. lia. }
  assert (HBBS : 0 < A + 4096 /\ A + 4096 + 16 <= alloc_ceiling /\ (A + 4096 + 16 <= SB \/ SB + kSpaceSize <= A + 4096)) by (clear -AHI L1 CBHI KNr M3 OUT; subst n; lia).
  assert (HC4 : CTX + 4096 <= alloc_ceiling) by (clear -IA2 WE26; lia).
  assert (HTPA : PA + 8 * (Z.of_nat (length cs) + Z.of_nat (length junk)) <= T \/ T + 4096 <= PA) by (rewrite LENCS; unfold kChunksBlockCount; clear -WE23; lia).
  assert (RSVT : forall sc', In sc' (as_sec a) -> sc_map_beg sc' + sc_map_size sc' <= T \/ T + 4096 <= sc_map_beg sc')
    by (intros sc' Hsc'; destruct (S3 sc' Hsc') as (_ & _ & _ & _ & _ & _ & RSV); exact (RSV _ WE13)).
  assert (RSVC : forall sc', In sc' (as_sec a) -> sc_map_beg sc' + sc_map_size sc' <= CTX \/ CTX + 4096 <= sc_map_beg sc').
  { intros sc' Hsc'. destruct (S3 sc' Hsc') as (_ & _ & _ & _ & _ & _ & RSV). pose proof CR0 as (CIN & _). pose proof (RSV _ CIN) as X. cbn [fst snd] in X.
    pose proof (RSV _ WE24) as Y. cbn [fst snd] in Y. unfold kIArenaLen in Y. clear -Y IA1 IA2. lia. }
  assert (HTL : forall jx c', nth_error cs jx = Some c' -> fst c' + snd c' <= T \/ T + 4096 <= fst c').
  { intros jx c' Hj. destruct (CSA jx c' Hj) as (sc' & Hsc' & -> & ->). exact (RSVT sc' Hsc'). }
  assert (HCL : forall jx c', nth_error cs jx = Some c' -> fst c' + snd c' <= CTX \/ CTX + 4096 <= fst c').
  { intros jx c' Hj. destruct (CSA jx c' Hj) as (sc' & Hsc' & -> & ->). exact (RSVC sc' Hsc'). }
  assert (HTCB : cb + 16 <= T \/ T + 4096 <= cb) by (pose proof (RSVT sc Hsc) as X; fold A L in X; clear -X L1 CBHI KNr; subst n; lia).
  (* [comment removed for export] *)
  set (nhi := n / 2^32). set (nlo := n mod 2^32).
  assert (HNHI : 0 <= nhi < 256) by (subst nhi; clear -KNr; subst n; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (HNLO : 0 <= nlo < 2^32) by (subst nlo; clear; apply Z.mod_pos_bound; lia).
  assert (En : n = nhi * 2^32 + nlo) by (subst nhi nlo; clear -KNr; rewrite Z.mul_comm; apply Z_div_mod_eq_full).
  destruct (Rch _ _ Hcm) as [_ ((b1 & HB1x & HDRb) & _ & _)]. rewrite ST in HDRb. cbn [hdr_state hdr_alloc_id] in HDRb. rewrite <- ECB in HDRb. fold n in HDRb.
  set (b1' := b1 mod 256). assert (HB1 : 0 <= b1' < 256) by (subst b1'; clear; apply Z.mod_pos_bound; lia).
  assert (HDR : rw_cells bsegs m cb [C4 (wz (3 + 256 * (b1' + 256 * nhi))); C4 (wz nlo); C8 (wz i)]).
  { rewrite En in HDRb. fold nhi in HDRb.
    replace (Z_to_bv 8 b1) with (Z_to_bv 8 b1') in HDRb by (subst b1'; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; rewrite Z.mod_mod by (clear; lia); reflexivity).
    generalize HDRb. clear -HNHI HNLO HB1. intros HDRb.
    eapply BF_free_kit.rw_cells_reshape; [| | exact HDRb]; [cbn; tauto|].
    cbn [cells_bytes cbytes map app]. unfold le4, le2, le1. rewrite !Z_to_bv_unsigned. cbn [Z_to_le_bytes map app].
    rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64).
    unfold kChunkQuarantine. rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite ?app_nil_r.
    rewrite !(Z.mod_small _ (2^64)) by lia.
    repeat (apply f_equal2; [Z.div_mod_to_equations; lia|]). reflexivity. }
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (wz SB); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz RI)] [C1 (Z_to_bv 8 0)] I1) as [INS4 _].
  pose proof Rins as (_ & _ & I3 & I4 & _ & I6 & I7 & _). unfold ae_instance in I3, I4, I6, I7. rewrite IC0 in I3, I4, I6, I7.
  cbn [aic_instance both_ic kInsNReserved kInsSecStats kInsSecMutex kInsGlobalStats Z.add] in I3, I4, I6, I7.
  pose proof (BF_kit3.rwc_split bsegs m _ [C8 (AsanRep.zw kPageSize); C8 (AsanRep.zw (ae_ptr_array E0))] [C8 (AsanRep.zw (ae_ptr_array E0)); C8 (AsanRep.zw (2^23))] I2) as [SEC _].
  fold PA in SEC. change kPageSize with 4096 in SEC.
  assert (NRS : rw_cells bsegs m 0xaafc8 [C8 (wz (as_ptr_committed a)); C8 (wz (Z.of_nat (length cs))); C1 (Z_to_bv 8 0)]) by (rewrite LENcs; unfold n_chunks in I3; exact I3).
  assert (ARR : u64arr bsegs m PA (gws cs junk)).
  { unfold gws. subst cs. rewrite map_map. cbn [fst]. exact PARRm. }
  assert (HDRS : forall jx c', nth_error cs jx = Some c' -> exists nd, rw_cells bsegs m (fst c') [C8 (wz (fst c')); C8 (wz (snd c')); C8 nd; C8 (wz (Z.of_nat jx))]).
  { intros jx c' Hj. subst cs. rewrite nth_error_map in Hj. destruct (nth_error (as_sec a) jx) as [sc'|] eqn:Ej; [| discriminate]. injection Hj as <-. cbn [fst snd].
    destruct (HDRSm jx sc' Ej) as [X _]. exists (AsanRep.zw (sc_needed sc')). exact X. }
  set (rf := ts_real_frees (as_ts a) mod 2^64). set (rfd := ts_really_freed (as_ts a) mod 2^64).
  assert (TST : rw_cells bsegs m (T + 2840) [C8 (wz rf); C8 (wz rfd)]).
  { pose proof (BF_tkit.u64arr_cell m _ _ 5 _ Tst eq_refl) as X5. pose proof (BF_tkit.u64arr_cell m _ _ 6 _ Tst eq_refl) as X6.
    pose proof (BF_kit3.rwc_join_at bsegs m _ _ _ _ X5 X6 ltac:(cbn; clear; lia)) as X. cbn [app] in X. unfold kThrStats in X.
    replace (T + 2800 + 8 * Z.of_nat 5) with (T + 2840) in X by (clear; lia). subst rf rfd. rewrite !BF_popT.wz_mod. exact X. }
  (* [comment removed for export] *)
  set (P0 := PP s mo).
  pose proof (BF_caT.PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo R0 R0' ATK) as KIP0.
  assert (AKs : AKern E0 (aps_alloc s) mo) by exact AK.
  assert (PSTK : forall y k, lo <= y -> y + Z.of_nat k <= usp -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_stack' E0 FSB0 HR0 s mo AKs WE ENV0); clear -H1 H2 LOC SPH CR; lia. }
  assert (PDAT : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_img' E0 FSB0 HR0 s mo AKs WE ENV ENV0); clear -H1 H2; lia. }
  assert (PT : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_thread' E0 FSB0 HR0 s mo AKs WE); assumption. }
  assert (PCTX : P0 (Z_to_bv 64 (CTX + 152), 8%nat)).
  { unfold P0, BF_caT.PP. apply (pol_resv_range' E0 FSB0 HR0 s mo AKs c0 cl _ _ CR0); clear -CC1 CC2; cbn; lia. }
  assert (PCH : forall y k, cb <= y -> y + Z.of_nat k <= cb + 16 -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_sec_map E0 FSB0 HR0 s mo [] D AKs WF sc y k Hsc); fold A L; clear -H1 H2 L1 CBHI KNr; subst n; lia. }
  assert (PARR : forall y k, PA <= y -> y + Z.of_nat k <= PA + 8 * Z.of_nat (length cs) -> P0 (Z_to_bv 64 y, k)).
  { intros y k H1 H2. unfold P0, BF_caT.PP. apply (pol_ptr_head' E0 FSB0 HR0 s mo AKs WE); [exact PTRC| exact H1| unfold kPtrArrayCommit; rewrite LENcs in H2; unfold kChunksBlockCount in PLEN; clear -H2 PLEN; lia]. }
  assert (PHDR : forall jx c' y k, nth_error cs jx = Some c' -> fst c' <= y -> y + Z.of_nat k <= fst c' + 32 -> P0 (Z_to_bv 64 y, k)).
  { intros jx c' y k Hj H1 H2. destruct (CSA jx c' Hj) as (sc' & Hsc' & E1 & E2). unfold P0, BF_caT.PP.
    destruct (S3 sc' Hsc') as (_ & _ & _ & Q4 & Q5 & _). change kPageSize with 4096 in Q5.
    apply (pol_sec_map E0 FSB0 HR0 s mo [] D AKs WF sc' y k Hsc'); rewrite <- ?E1; [exact H1| clear -H2 Q4 Q5 E1; rewrite E1 in H2; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  set (st := as_sec_stats a).
  set (nf := ss_n_frees st mod 2^64). set (cur := ss_cur st mod 2^64).
  set (ga := as_glob_allocated a mod 2^64). set (gm := as_glob_mapped a mod 2^64).
  assert (HV : 0 <= nf < 2^64 /\ 0 <= cur < 2^64 /\ 0 <= ga < 2^64 /\ 0 <= gm < 2^64) by (subst nf cur ga gm; clear; Z.div_mod_to_equations; lia).
  assert (SST : rw_cells bsegs m 0xaafe0 [C8 (wz (ss_n_allocs st)); C8 (wz nf); C8 (wz cur); C8 (wz (ss_max st))]) by (subst nf cur st; rewrite !BF_popT.wz_mod; exact I4).
  assert (GST : rw_cells bsegs m 0xab218 [C8 (wz ga); C8 (wz gm)]) by (subst ga gm; rewrite !BF_popT.wz_mod; exact I7).
  assert (MTX : rw_cells bsegs m 0xab200 [C4 (wz 0)]) by exact I6.
  destruct (HDRSm ix sc NTH) as [HDRC _]. fold A L in HDRC.
  set (mu := ts_munmaps (as_ts a) mod 2^64). set (mud := ts_munmaped (as_ts a) mod 2^64).
  assert (TST2 : rw_cells bsegs m (T + 2888) [C8 (wz mu); C8 (wz mud)]).
  { pose proof (BF_tkit.u64arr_cell m _ _ 11 _ Tst eq_refl) as X5. pose proof (BF_tkit.u64arr_cell m _ _ 12 _ Tst eq_refl) as X6.
    pose proof (BF_kit3.rwc_join_at bsegs m _ _ _ _ X5 X6 ltac:(cbn; clear; lia)) as X. cbn [app] in X. unfold kThrStats in X.
    replace (T + 2800 + 8 * Z.of_nat 11) with (T + 2888) in X by (clear; lia). subst mu mud. rewrite !BF_popT.wz_mod. exact X. }
  assert (AM8 : A mod 8 = 0) by (clear -M1; Z.div_mod_to_equations; lia).
  assert (SHJ : exists shj, rw_cells bsegs m (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) shj]).
  { apply (shadow_join_any m kShadowBase (A / 8) (Z.to_nat (L / 8))); [| clear -M4 M5; Z.div_mod_to_equations; lia].
    intros g Hg. rewrite Z2Nat.id in Hg by (clear -M4 M5; Z.div_mod_to_equations; lia).
    assert (HSM : in_some_sec_map a (8 * g) = true).
    { unfold in_some_sec_map. apply (proj2 (existsb_exists _ _)). exists sc. split; [exact Hsc|]. fold A L.
      apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; clear -Hg AM8 M4 M5; Z.div_mod_to_equations; lia. }
    assert (HS : exists v, Sh E0 a (8 * g) = Some v) by (unfold Sh; rewrite HSM, orb_true_r; eexists; reflexivity).
    destruct HS as [v Hv]. exists (Z_to_bv 8 v). exact (Rsh g v Hv). }
  destruct SHJ as [shj SHJ].
  destruct (BF_statics.guard_cell m) as [cnr CNR]. pose proof (ld_statics_of a m cnr IC0 REP RT CNR) as LDS.
  (* [comment removed for export] *)
  set (a1 := upd_chunks (delete cb) (upd_ts (ts_on_real_free n) a)).
  set (Q1 := fun ms' : machine_state => exists (m1 : mem) (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ms' = MS (mkR ra (wz usp) gp tp t0' t1' t2' s0 s1 (wz 0xaaf98) (wz 0xab208) (wz (A + 4096)) a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz 0x35230) fc None m1 (seg_rom bsegs)
        /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp
        /\ munch [(usp - 80, usp); (0xab200, 0xab204); (T + 2840, T + 2856)] m m1 /\ wmono bsegs m m1
        /\ rw_cells bsegs m1 0xaaf98 [C8 (wz 4096); C8 (wz PA)]
        /\ rw_cells bsegs m1 0xaafc8 [C8 (wz (as_ptr_committed a)); C8 (wz (Z.of_nat (length cs))); C1 (Z_to_bv 8 0)]
        /\ rw_cells bsegs m1 0xab200 [C4 (wz 0)]
        /\ u64arr bsegs m1 PA (gws cs junk)
        /\ (forall jx c', nth_error cs jx = Some c' -> exists nd, rw_cells bsegs m1 (fst c') [C8 (wz (fst c')); C8 (wz (snd c')); C8 nd; C8 (wz (Z.of_nat jx))])
        /\ thread_cells m1 tp 0x6028f8 CTX T
        /\ rw_cells bsegs m1 (T + 2840) [C8 (wz (rf + 1)); C8 (wz (n + rfd))]).
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) P0 Q1).
  { eapply (qcbr_sec_walk P0 ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc Q1 usp lo CBP cb SB RI b1' nhi nlo (wz i) PA cs junk
              (as_ptr_committed a) (A + 4096) 0x6028f8 CTX T rf rfd c0 cl
              LOC ltac:(clear -LO; lia) ltac:(clear -SPH; lia) HSB HCB HCBS HB1 HNHI HNLO HPA RNG HBB HBBS ltac:(clear; lia) ltac:(clear; lia)
              ltac:(clear -CQ1 CQ2 CQ3 CC1 CC2; lia) HC4 TR2 ltac:(rewrite TP, unsigned_lit by (clear; lia); clear; lia)
              ltac:(subst rf; apply Z.mod_pos_bound; clear; lia) ltac:(subst rfd; apply Z.mod_pos_bound; clear; lia) HTPA HTL HTCB CT
              PSTK PDAT PCH PARR PHDR PCTX PT m MI SK INS4 ltac:(unfold BF_free5s.hk; exact HDR) SEC NRS MTX ARR HDRS TC TST).
    intros m1 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' MI1 SK1 MU1 WM1 INS1 HDR1 SEC1 NRS1 MTX1 ARR1 HDRS1 TC1 TST1.
    apply evtA_done. unfold Q1. exists m1, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
    unfold BF_free5s.n in TST1. rewrite <- En in TST1.
    repeat match goal with |- _ /\ _ => split end; first [reflexivity| assumption]. }
  { exact KIP0. }
  intros ms1 mo1 HQ1 AG1 KIP1. unfold Q1 in HQ1.
  destruct HQ1 as (m1 & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & MI1 & SK1 & MU1 & WM1 & SEC1 & NRS1 & MTX1 & ARR1 & HDRS1 & TC1 & TST1).
  pose proof (magree_frame _ _ AG1) as (Ffds1 & Fvm1 & Flz1 & Ffs1 & Fh1 & Ftid1 & _). destruct KIP1 as [KIA1 _].
  pose proof L0OK as (LS_L0 & GS_L0 & HS_L0 & RES0_low & RES0_cover & RSVD & RSVD_pos).
  (* [comment removed for export] *)
  assert (LBIG : 4096 + 16 <= L) by (clear -L1 CBHI KNr; subst n; lia).
  assert (NMI : forall z, ~ in_cells img_mut z -> ~ (0xaaf58 <= z < 0xaaf58 + 3632)).
  { intros z NM R. apply NM. exists (aic_instance both_ic, 3632). split; [unfold img_mut; left; reflexivity| cbn [fst snd aic_instance both_ic]; exact R]. }
  assert (SECNE : as_sec a <> []) by (intros E; rewrite E in Hsc; exact Hsc).
  set (lsc := List.last (as_sec a) sc).
  assert (LASTIN : In lsc (as_sec a)) by (subst lsc; apply last_In; exact SECNE).
  assert (LASTEQ : fst (List.last cs (sc_map_beg sc, sc_map_size sc)) = sc_map_beg lsc).
  { subst cs lsc. pose proof (last_map_gen (fun c => (sc_map_beg c, sc_map_size c)) (as_sec a) sc) as X. cbn beta in X. rewrite X. reflexivity. }
  destruct (S3 lsc LASTIN) as (Ml1 & Ml2 & Ml3 & Ml4 & Ml5 & Ml6 & Ml7). change kPageSize with 4096 in Ml1, Ml5. pose proof (SECHI lsc LASTIN) as LHI.
  pose proof (Ml7 _ WE13) as LvT. cbn [fst snd] in LvT.
  pose proof CR0 as (CIn & _ & _ & _ & _ & _ & CPA & _). pose proof DR0 as (DIn & _ & _ & _ & _ & _ & DPA & _). unfold kPtrArrayLen in CPA, DPA. fold PA in CPA, DPA.
  pose proof (Ml7 _ CIn) as LvC. cbn [fst snd] in LvC. pose proof (Ml7 _ DIn) as LvD. cbn [fst snd] in LvD.
  pose proof (M7 _ CIn) as AvC. cbn [fst snd] in AvC. pose proof (M7 _ DIn) as AvD. cbn [fst snd] in AvD. fold A L in AvC, AvD.
  pose proof (RSVT sc Hsc) as AvT. fold A L in AvT.
  assert (IXLT : (ix < length cs)%nat) by exact (nth_error_lt _ _ _ NTHcs).
  assert (LSZ : 4096 <= sc_map_size lsc) by (clear -Ml4 Ml5; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  Ltac trs1 H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn].
  assert (SST1 : rw_cells bsegs m1 0xaafe0 [C8 (wz (ss_n_allocs st)); C8 (wz nf); C8 (wz cur); C8 (wz (ss_max st))]).
  { trs1 SST MU1 WM1. clear -LOC LO CR Timg. repeat split; try exact I; lia. }
  assert (GST1 : rw_cells bsegs m1 0xab218 [C8 (wz ga); C8 (wz gm)]).
  { trs1 GST MU1 WM1. clear -LOC LO CR Timg. repeat split; try exact I; lia. }
  assert (HDRC1 : rw_cells bsegs m1 A [C8 (AsanRep.zw A); C8 (AsanRep.zw L); C8 (AsanRep.zw (sc_needed sc)); C8 (AsanRep.zw (Z.of_nat ix))]).
  { trs1 HDRC MU1 WM1. clear -LOC LO AHI M3 LBIG AvT. repeat split; try exact I; lia. }
  assert (TST21 : rw_cells bsegs m1 (T + 2888) [C8 (wz mu); C8 (wz mud)]).
  { trs1 TST2 MU1 WM1. clear -LOC LO Thi Timg. repeat split; try exact I; lia. }
  assert (SHJ1 : rw_cells bsegs m1 (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) shj]).
  { eapply rw_cells_transport; [exact SHJ| exact MU1| exact WM1|]. cbn [cells_size csize disjoint_from]. rewrite ?Nat.add_0_r, Z2Nat.id by (clear -M4; Z.div_mod_to_equations; lia).
    unfold kShadowBase.
    clear -LOC LO CR AHI M3 M4 Tband. repeat split; try exact I; Z.div_mod_to_equations; lia. }
  assert (LDS1 : ld_statics m1 cnr).
  { apply (ld_statics_agree m m1 cnr LDS). intros x Hx. unfold ld_static_addr in Hx. apply MU1. rewrite wa_unsigned by (clear -Hx; lia).
    cbn [outside]. clear -Hx LOC LO CR Timg. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  pose proof (RTOK_magree _ _ _ _ _ _ _ _ _ _ _ TOK AG1 KIA1) as TOK1.
  assert (TOK1' : RTOKc C C' (sA a1 s) mo1).
  { apply (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 C C' s a a1 mo1).
    - change a with (aps_alloc s). rewrite BF_popT.sA_self. exact TOK1.
    - unfold same_fp. repeat split; reflexivity.
    - reflexivity. - reflexivity. }
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK1') as (R1 & R1' & ATK1 & HCR1 & HCR1' & GR1 & GD1 & GLE1).
  assert (AK1 : AKern E0 a1 mo1).
  { apply (AKern_ext E0 a a1); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity|]. exact (AKern_frame _ _ _ _ Fvm1 Flz1 AK). }
  assert (WF1 : AWf E0 [] D a1).
  { subst a1. pose proof (AWf_delete_chunk E0 [] D (upd_ts (ts_on_real_free n) a) cb (fun d => d)) as X. rewrite AsanWf8.upd_dead_id in X.
    apply X; [| cbn [as_tq as_gq upd_ts]; exact NIB]. eapply AWf_same_core; [apply same_core_upd_ts| exact WF]. }
  assert (HabK : cm_alloc_beg cm = sc_map_beg sc + kPageSize) by (rewrite Hab; reflexivity).
  destruct (run_qcbr_sec E0 [] D a cb cm sc ix i j [] WF Hcm ST PC NTH HabK) as [f RUN].
  pose proof (B_live.hoare_arun _ _ _ a f _ _ _ _ _ (qcb_recycle_spec E0 [] D a cb cm i j WF Hcm ST NIB) eq_refl RUN) as (WFa' & CHa' & TQa' & GQa').
  assert (DISJPA : forall jx c', nth_error cs jx = Some c' -> PA + 8 * kChunksBlockCount <= fst c' \/ fst c' + snd c' <= PA).
  { intros jx c' Hj. destruct (CSA jx c' Hj) as (sc' & Hsc' & E1 & E2). destruct (S3 sc' Hsc') as (_ & _ & _ & _ & _ & _ & RSV).
    pose proof (RSV _ WE8) as X. cbn [fst snd] in X. rewrite E1, E2. change kChunksBlockCount with 16384. clear -X. lia. }
  assert (HCP : PA + 8 * kChunksBlockCount <= CTX \/ CTX + 160 <= PA) by (change kChunksBlockCount with 16384; clear -CPA CC1 CC2; lia).
  assert (HTP2 : PA + 8 * kChunksBlockCount <= T \/ T + 4096 <= PA) by (change kChunksBlockCount with 16384; clear -WE23; lia).
  assert (PERM : Permutation (as_sec a) (as_sec (ldl_st cb cm sc ix a) ++ [sc])).
  { rewrite ldl_as_sec. eapply Permutation_trans; [apply Permutation_sym; exact (AsanWf8.swap_remove_perm (as_sec a) ix sc NTH)| apply Permutation_cons_append]. }
  (* [comment removed for export] *)
  eapply (ldealloc_srz E0 FSB0 HR0 L0 RES0 EB0 HR0_ok ENV0 LS_L0 HS_L0 RES0_low (sA a1 s) (ldl_st cb cm sc ix a) sc [] D
            PERM eq_refl (fun c' => eq_refl) eq_refl eq_refl eq_refl WF1 RES PTRC (ex_intro _ [] (ex_intro _ D WFa'))
            cs junk ix (as_ptr_committed a) (ss_n_allocs st) nf cur (ss_max st) ga gm mu mud (AsanRep.zw (sc_needed sc)) 0x6028f8 CTX T c0 cl cnr shj
            NTHcs CSA LENCS RNG DISJ HV eq_refl ltac:(clear; lia) ltac:(clear; lia) (conj CR0 (conj CC1 CC2)) HC4 CT TR2 HTL HCL DISJPA HTP2 HCP
            ra gp tp t0' t1' t2' s0 s1 a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' F fc m1 mo1 usp lo R1 R1' K KN ATK1 AK1 SPA SK1 LOC
            ltac:(clear -LO; lia) ltac:(clear -SPH; lia) MI1 ltac:(rewrite TP; apply unsigned_lit; clear; lia) SEC1 NRS1 SST1 MTX1 GST1 ARR1 HDRS1 HDRC1 TC1 TST21 LDS1 SHJ1).
  intros ms' mo' POST. unfold ld_post in POST.
  destruct POST as (t0x & t1x & t2x & a0x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m' & -> & MI' & SK' & MU' & MTX' & NRS' & SST' & GST' & ARR' & HDRS' & TST2' & TC' & LDS' & SHZ' & ATK' & AK' & Ffs' & Ffds' & Ftid').
  rewrite unsigned_lit in SK' by (clear -USPR; lia). rewrite unsigned_lit in MU' by (clear -USPR; lia). rewrite LASTEQ in MU'.
  (* [comment removed for export] *)
  assert (AG7 : forall z, 0 <= z < 2^64 -> ~ FPW7 a lo sc ix z -> m' (wa z) = m (wa z)).
  { intros z Hz NF. unfold FPW7 in NF. cbv zeta in NF. unfold ae_instance in NF. rewrite IC0 in NF.
    cbn [aic_instance both_ic] in NF. unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats, kShadowBase in NF. fold PA A L lsc in NF.
    transitivity (m1 (wa z)).
    - apply MU'. rewrite wa_unsigned by exact Hz. cbn [outside]. unfold kShadowBase. clear -NF LO Hz. repeat split; try exact I; lia.
    - apply MU1. rewrite wa_unsigned by exact Hz. cbn [outside]. clear -NF LO Hz. repeat split; try exact I; lia. }
  (* [comment removed for export] *)
  pose proof (renv_of E0 PL0 ENV0 PL0OK D a mo WF AK EI1 EI2) as RENV.
  assert (REP' : ARep bsegs E0 (DepotR bsegs E0) (ldl_st cb cm sc ix a) m').
  { apply (R7 a m m' lo cb i j ix D cm sc (wz (sc_map_beg lsc) :: junk) Hcm ST PC NTH HabK REP WF RENV AG7 LOC);
      unfold ae_instance; rewrite ?IC0; cbn [aic_instance both_ic]; unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats; cbn [Z.add]; fold lsc A L.
    - unfold n_chunks. rewrite <- LENcs. exact NRS'.
    - fold st. subst nf cur. rewrite BF_popT.wz_mod_add in SST'.
      replace (ss_cur st mod 2 ^ 64 - L) with (ss_cur st mod 2 ^ 64 + - L) in SST' by (clear; lia). rewrite BF_popT.wz_mod_add in SST'.
      replace (ss_cur st + - L) with (ss_cur st - L) in SST' by (clear; lia). exact SST'.
    - exact MTX'.
    - subst ga gm. replace (as_glob_allocated a mod 2 ^ 64 - L) with (as_glob_allocated a mod 2 ^ 64 + - L) in GST' by (clear; lia).
      replace (as_glob_mapped a mod 2 ^ 64 - L) with (as_glob_mapped a mod 2 ^ 64 + - L) in GST' by (clear; lia).
      rewrite !BF_popT.wz_mod_add in GST'. replace (as_glob_allocated a + - L) with (as_glob_allocated a - L) in GST' by (clear; lia).
      replace (as_glob_mapped a + - L) with (as_glob_mapped a - L) in GST' by (clear; lia). exact GST'.
    - rewrite ldl_as_sec. cbv delta [lsc]. unfold gws in ARR'. cbv delta [cs] in ARR'. rewrite map_map in ARR'. cbn beta in ARR'. cbn [fst] in ARR'.
      pose proof (last_map_gen (fun c => (sc_map_beg c, sc_map_size c)) (as_sec a) sc) as LM. cbn beta in LM. rewrite LM in ARR'. cbn [fst] in ARR'.
      pose proof (swap_words (as_sec a) junk ix sc NTH) as SW. cbn beta in SW. rewrite SW in ARR'. cbn beta. exact ARR'.
    - rewrite ldl_as_sec. unfold AsanOps.removelast. rewrite length_firstn, length_list_set. cbn [length].
      assert (LPOS : (0 < length (as_sec a))%nat) by (destruct (as_sec a); [exfalso; exact (SECNE eq_refl)| cbn; clear; lia]).
      apply Nat2Z.inj. rewrite Z2Nat.id by (unfold kChunksBlockCount; clear; lia). rewrite <- LENCS, LENcs. clear -LPOS. lia.
    - intros NEQ.
      assert (IXNE : ix <> Nat.pred (length cs)).
      { intros E. apply NEQ. subst lsc. pose proof (last_nth (as_sec a) sc SECNE) as X. rewrite <- LENcs, <- E, NTH in X. injection X as X. rewrite <- X. reflexivity. }
      assert (NTH' : nth_error (AsanOps.removelast (BF_ldealloc1.list_setn cs ix (List.last cs (sc_map_beg sc, sc_map_size sc)))) ix
                       = Some (List.last cs (sc_map_beg sc, sc_map_size sc))).
      { unfold AsanOps.removelast. rewrite BF_ldealloc4.length_list_setn. rewrite nth_error_firstn_lt by (clear -IXLT IXNE; lia).
        rewrite list_setn_upd. apply nth_error_upd_same. exact IXLT. }
      destruct (HDRS' ix _ NTH') as [nd Hnd]. rewrite LASTEQ in Hnd.
      pose proof (BF_kit3.rwc_split bsegs m' _ [C8 (wz (sc_map_beg lsc)); C8 (wz (snd (List.last cs (sc_map_beg sc, sc_map_size sc)))); C8 nd] [C8 (wz (Z.of_nat ix))] Hnd) as [_ X].
      cbn [cells_size csize Z.add Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in X. exact X.
    - eapply (rw_cells_agree bsegs m1 m').
      2:{ subst rf rfd. rewrite !BF_popT.wz_mod_add in TST1. rewrite (Z.add_comm n) in TST1. rewrite BF_popT.wz_mod_add in TST1.
          replace (T + 2840) with (T + 2800 + 40) in TST1 by (clear; lia). exact TST1. }
      cbn. intros x Hx. apply MU'. rewrite wa_unsigned by (clear -Hx Thi Tlo CR; lia). cbn [outside]. unfold kShadowBase.
      clear -Hx LOC LO CR Thi Tlo Timg Tband AvT LvT LSZ HTP2 AHI M3 M4 IXLT LENCS. change kChunksBlockCount with 16384 in HTP2. unfold kChunksBlockCount in LENCS.
      repeat split; try exact I; Z.div_mod_to_equations; lia.
    - subst mu mud. rewrite !BF_popT.wz_mod_add in TST2'. replace (T + 2888) with (T + 2800 + 88) in TST2' by (clear; lia). exact TST2'.
    - exact SHZ'. }
  (* [comment removed for export] *)
  rewrite BF_popT.sA_sA in ATK'.
  assert (TOK' : RTOKc C C' (sA (ldl_st cb cm sc ix a) s) mo').
  { apply (RTOK_intro E0 FSB0 HR0 L0 RES0 EB0 C C' _ mo' R1 R1' ATK'); cbn [aps_alloc sA aps_set_alloc]; cbn [aps_alloc sA aps_set_alloc] in GR1, GD1, GLE1.
    - clear -HCR1; lia.
    - rewrite (gapR_eq a1 (ldl_st cb cm sc ix a) eq_refl (regions_bytes_same a1 _ (fun c' => eq_refl))). exact GR1.
    - rewrite (gapD_eq a1 (ldl_st cb cm sc ix a) eq_refl eq_refl eq_refl). exact GD1.
    - rewrite (gapR_eq a1 (ldl_st cb cm sc ix a) eq_refl (regions_bytes_same a1 _ (fun c' => eq_refl))).
      rewrite (gapD_eq a1 (ldl_st cb cm sc ix a) eq_refl eq_refl eq_refl). rewrite (gapP_eq a1 (ldl_st cb cm sc ix a) eq_refl). exact GLE1.
    - clear -HCR1'; lia. }
  (* [comment removed for export] *)
  assert (RT' : rt_misc5 FSB0 PL0 E0 m').
  { apply (rt_misc5_agree E0 FSB0 PL0 m m' RT). intros z Hz.
    destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
    - pose proof (NMI z NM) as NI. apply AG7; [clear -ZI; lia|]. intros FW. unfold FPW7 in FW. cbv zeta in FW. unfold ae_instance in FW. rewrite IC0 in FW.
      cbn [aic_instance both_ic] in FW. unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats, kShadowBase in FW. fold PA A L lsc in FW.
      clear -FW ZI NI LOC CR PA0 LHI Timg AHI. Z.div_mod_to_equations. lia.
    - unfold rt_high2 in RH. apply AG7; [clear -RH Tlo Thi CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CR; lia|]. intros FW. unfold FPW7 in FW. cbv zeta in FW. unfold ae_instance in FW. rewrite IC0 in FW.
      cbn [aic_instance both_ic] in FW. unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats, kShadowBase in FW. fold PA A L lsc in FW.
      change kChunksBlockCount with 16384 in HCP, HTP2.
      destruct FW as [FW|[FW|[FW|[FW|[FW|[FW|[FW|[FW|[FW|[FW|FW]]]]]]]]]].
      + clear -FW RH LOC Thi CQ2 CC2 DQ2 DD2. lia.
      + clear -FW RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
      + clear -FW RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
      + clear -FW RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
      + clear -FW RH Timg Tlo CQ3 CC1 CC2 DQ3 DD1 DD2. lia.
      + clear -FW RH HTP2 HCP DPA DD1 DD2 IXLT LENCS. unfold kChunksBlockCount in LENCS. lia.
      + clear -FW RH LvT LvC LvD CC1 CC2 DD1 DD2 LSZ. lia.
      + clear -FW RH CT DT. lia.
      + clear -FW RH CT DT. lia.
      + clear -FW RH Tband CQ4 CC1 CC2 DQ4 DD1 DD2 CR AHI M3 M4. Z.div_mod_to_equations. lia.
      + clear -FW RH AvT AvC AvD CC1 CC2 DD1 DD2. lia. }
  (* [comment removed for export] *)
  eapply KONT. unfold item_post.
  split. { exists f, (sec_orc A L ++ []), (sec_evs A L), []. exact RUN. }
  split; [exact REP'|]. split; [exact WFa'|]. split; [exact AK'|]. split; [exact TOK'|].
  split; [rewrite Ffs'; exact Ffs1|]. split; [rewrite Ffds'; exact Ffds1|]. split; [rewrite Ftid'; exact Ftid1|].
  split; [exact SK'|]. split; [exact MI'|]. split; [exact RT'|].
  split. { unfold item_W. rewrite PC. cbv zeta. fold n. rewrite Hab, <- Hms. fold L. replace (A + 4096 - kPageSize) with A by (unfold kPageSize; clear; lia).
           assert (LB : last_beg a = sc_map_beg lsc).
           { unfold last_beg. subst lsc. destruct (exists_last SECNE) as (l' & x & E). rewrite E. rewrite rev_app_distr. cbn [rev app]. rewrite (List.last_last l' x sc). reflexivity. }
           rewrite LB. unfold K_ITEM, kThrStats, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats. change kChunksBlockCount with 16384.
           eapply munch_trans.
           - eapply munch_cover; [exact MU1|]. clear -LO. solve_covers.
           - eapply munch_cover; [exact MU'|]. unfold kShadowBase. clear -LO IXLT LENCS. unfold kChunksBlockCount in LENCS. solve_covers. }
  unfold item_same. rewrite PC. split.
  - unfold item_sameC. rewrite ldl_as_chunks, ldl_as_tq, ldl_as_gq, ldl_as_ptr_committed, ldl_as_nprim_ever, ldl_as_residue, ldl_as_everc, ldl_as_ndepot_ins,
      ldl_as_node_blocks, ldl_as_store_blocks, ldl_as_keys, ldl_as_frames, ldl_as_store_stored, ldl_as_cache_inited, ldl_as_cache_mapped, ldl_as_ia_inited, ldl_as_oom,
      regions_bytes_ldl.
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try (clear; lia); try (unfold kFreeArrayMapSize; clear; lia).
    + exact CI.
    + intros c'. rewrite ldl_get_region. split; reflexivity.
    + apply (live_blocks_del_quar a _ cb cm i j Hcm ST). apply ldl_as_chunks.
  - unfold item_sameS. exists sc. split; [exact Hsc|]. split; [exact HabK|]. split; [exact Hms|].
    split; [rewrite ldl_as_sec; exact (AsanWf8.swap_remove_perm (as_sec a) ix sc NTH)|].
    split; [rewrite ldl_ss_cur; reflexivity|]. split; [rewrite ldl_ss_max; reflexivity|]. intros c'. apply ldl_get_region.
Qed.

End DeallocT6.
End RC__1.
(* [comment removed for export] *)
