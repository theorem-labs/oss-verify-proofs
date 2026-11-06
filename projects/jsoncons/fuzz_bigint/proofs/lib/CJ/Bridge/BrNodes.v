(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  Scfg ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk AgentLib AgentNodes SpecConsts RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import MState ITree.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Nodes.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation cjnode := OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib.Nodes.node.
Notation cj_at_node := OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib.Nodes.at_node.
Import OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib.Nodes (NBrk, NMmap, NMunmap, NMprotect, areg).

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.

(* [comment removed for export] *)
Lemma gpr_areg0 : forall ms, ms_gpr ms 0 = areg ms 10. Proof. reflexivity. Qed.
Lemma gpr_areg1 : forall ms, ms_gpr ms 1 = areg ms 11. Proof. reflexivity. Qed.
Lemma gpr_areg2 : forall ms, ms_gpr ms 2 = areg ms 12. Proof. reflexivity. Qed.
Lemma gpr_areg3 : forall ms, ms_gpr ms 3 = areg ms 13. Proof. reflexivity. Qed.
Lemma gpr_areg4 : forall ms, ms_gpr ms 4 = areg ms 14. Proof. reflexivity. Qed.
Lemma gpr_areg5 : forall ms, ms_gpr ms 5 = areg ms 15. Proof. reflexivity. Qed.

Lemma u214 : bv_unsigned (Z_to_bv 64 214) = 214. Proof. reflexivity. Qed.
Lemma u215 : bv_unsigned (Z_to_bv 64 215) = 215. Proof. reflexivity. Qed.
Lemma u222 : bv_unsigned (Z_to_bv 64 222) = 222. Proof. reflexivity. Qed.
Lemma u226 : bv_unsigned (Z_to_bv 64 226) = 226. Proof. reflexivity. Qed.

Lemma lit_ne0 : forall z, 0 < z < 2 ^ 64 -> Z_to_bv 64 z <> Z_to_bv 64 0.
Proof.
  intros z Hz Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_brk_query : forall ms model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NBrk 0) ms ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (vm_brk (m_vmmaps model)) [] [] [] [] [])) model) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model K Hh Hlazy [Hsvc H10] Hc.
  apply (srz_brk_query_at segs scfg ms model (Z_to_bv 64 214) K Hh Hlazy Hsvc u214); [| exact Hc].
  rewrite gpr_areg0. exact H10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_brk_grow : forall ms model (d : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  cj_at_node segs (NBrk (bv_unsigned b + d)) ms ->
  bv_unsigned b mod page_size = 0 -> d mod page_size = 0 -> 0 < d ->
  0 < bv_unsigned b -> bv_unsigned b + d < 2 ^ 64 ->
  bv_unsigned (vm_start_brk h) <= bv_unsigned b + d ->
  (* [comment removed for export] *)
  srealizes segs scfg (mkCfg (nret ms (mkEffectU b [] [] [] [] [])) model) K ->
  (* [comment removed for export] *)
  (Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
   srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 (bv_unsigned b + d)) [] [(b, Z_to_bv 64 d)] [] [] []))
                        (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                                   (vm_noaccess h) (vm_start_brk h)
                                                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model d K Hh Hlazy h b [Hsvc H10] Hbal Hdal Hd Hb0 Hnw Hs HA HB.
  apply (srz_brk_grow_at segs scfg ms model (Z_to_bv 64 214) d K Hh Hlazy Hsvc u214 Halloc Hbal Hdal Hd Hb0 Hnw Hs);
    [rewrite gpr_areg0; exact H10 | intros _; exact HA | exact HB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mmap_rw : forall ms model (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMmap 0 len 3 34) ms -> 0 < len < 2 ^ 64 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok (Z_to_bv 64 0) model a n = true) ->
  (forall a, grant_ok (Z_to_bv 64 0) model a n = true ->
     srealizes segs scfg (mkCfg (nret ms (mkEffectU a [] [(a, Z_to_bv 64 n)] [] [] []))
                               (mmap_model a (Z_to_bv 64 n) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hlen n Hex HB.
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n) by (unfold page_round_up; rewrite Hu1; reflexivity).
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
    repeat split; try reflexivity. apply lit_ne0. lia. }
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (rewrite gpr_areg0; exact H10).
  eapply (srz_mmap segs scfg ms model (Z_to_bv 64 222) K Hh Hlazy Hsvc u222 Hargs Halloc).
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. apply HB. exact Ha.
  - rewrite H0, Hu1. exact Hex.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mmap_none : forall ms model (len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMmap 0 len 0 34) ms -> 0 < len < 2 ^ 64 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok_na (Z_to_bv 64 0) model a n = true) ->
  (forall a, grant_ok_na (Z_to_bv 64 0) model a n = true ->
     srealizes segs scfg (mkCfg (nret ms (mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] []))
                               (noaccess_model a (Z_to_bv 64 n) model)) K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hlen n Hex HB.
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
    repeat split; try reflexivity. apply lit_ne0. lia. }
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (rewrite gpr_areg0; exact H10).
  apply (srz_mmap_noaccess_at segs scfg ms model (Z_to_bv 64 222) K Hh Hlazy Hsvc u222 Hargs Halloc);
    rewrite H0, Hu1; [exact Hex | exact HB].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mmap_fixed : forall ms model (addr len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMmap addr len 0 50) ms ->
  addr mod page_size = 0 -> 0 < addr -> 0 < len ->
  addr + page_round_up_Z len <= alloc_top (m_vmmaps model) ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, n)] [] []))
                            (fixed_noaccess_model (Z_to_bv 64 addr) n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model addr len K Hh Hlazy (Hsvc & H10 & H11 & H12 & H13 & H14 & H15) Hal Hpos Hlen Htop n Hrf Hmc HB.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hprb.
  assert (Htop' : alloc_top (m_vmmaps model) < 2 ^ 64) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  assert (Haddr : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; lia).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok. rewrite gpr_areg1, gpr_areg2, gpr_areg3, gpr_areg4, gpr_areg5, H11, H12, H13, H14, H15.
    repeat split; try reflexivity. apply lit_ne0. lia. }
  apply (srz_mmap_fixed_noaccess_at segs scfg ms model (Z_to_bv 64 222) (Z_to_bv 64 addr) len K Hh Hlazy Hsvc u222 Hargs Halloc);
    rewrite ?gpr_areg0, ?gpr_areg1, ?Haddr; first [exact H10 | exact H11 | exact HB | assumption | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_mprotect : forall ms model (addr len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMprotect addr len 3) ms ->
  addr mod page_size = 0 -> 0 < len -> 0 <= addr ->
  addr + page_round_up_Z len < two_pow_64 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  map_contains (vm_maps (m_vmmaps model)) (Z_to_bv 64 addr) n = true ->
  mprotect_budget_ok model (Z_to_bv 64 addr) n = true ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, n)] [] [] []))
                            (mprotect_model (Z_to_bv 64 addr) n model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model addr len K Hh Hlazy (Hsvc & H10 & H11 & H12) Hal Hlen Ha0 Hnw n Hna Hma Hbud HB.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  assert (Haddr : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply u64_lit; unfold two_pow_64 in Hnw; lia).
  apply (srz_mprotect_at segs scfg ms model (Z_to_bv 64 226) (Z_to_bv 64 addr) len K Hh Hlazy Hsvc u226 Halloc);
    rewrite ?gpr_areg0, ?gpr_areg1, ?gpr_areg2, ?Haddr; first [exact H10 | exact H11 | exact H12 | exact HB | assumption | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bn_munmap : forall ms model (a len : Z) K,
  m_halted model = None -> m_vm_lazy model = [] ->
  cj_at_node segs (NMunmap a len) ms ->
  a mod page_size = 0 -> 0 <= a -> 0 < len ->
  a + page_round_up_Z len <= TASK_SIZE ->
  map_has (vm_maps (m_vmmaps model)) (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z len)) = true ->
  srealizes segs scfg (mkCfg (nret ms (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 a, Z_to_bv 64 (page_round_up_Z len))] [] []))
                      (munmap_model (Z_to_bv 64 a) (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros ms model a len K Hh Hlazy (Hsvc & H10 & H11) Hal Ha0 Hlen Hnw Hhas Hc.
  pose proof (page_round_up_Z_bounds len ltac:(lia)) as Hpr.
  assert (HTS : TASK_SIZE < 2 ^ 64) by (unfold TASK_SIZE; lia).
  assert (Haddr : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite gpr_areg1, H11; apply u64_lit; lia).
  assert (Hprr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)) by (unfold page_round_up; rewrite Hu1; reflexivity).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 a) by (rewrite gpr_areg0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hprr, Haddr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  eapply (SpinAlg.srz_munmap segs scfg ms model (Z_to_bv 64 215) K Hh Hlazy Hsvc u215 Hargs).
  unfold munmap_eff. rewrite H0, Hprr. exact Hc.
Qed.

End WithSegs.
