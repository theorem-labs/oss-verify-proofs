(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells SegD_wf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Record KD_laws2 (K : DG -> jpredA) (n : positive) (hc : Z) : Prop := mkKDL2 {
  kd2_stable : forall G, stableA segs n (K G);
  kd2_view : forall G rho rho' tp tr md,
      (forall i, rw rho' i = rw rho i) -> (forall l, rl rho' l = rl rho l) ->
      (forall z, ~ DFPw G z -> view segs (rm rho') z = view segs (rm rho) z) ->
      K G rho tp tr md -> K G rho' tp tr md;
  kd2_trans : forall G tp md G' tp' md' rho tr,
      dtrans G tp md G' tp' md' -> K G rho tp tr md -> K G' rho tp' tr md';

  kd2_room : forall G rho tp tr md, K G rho tp tr md -> depot_inv segs G rho md tp -> headroom md tp + dep_cost G >= hc;
  kd2_reserved : forall G rho tp tr md, K G rho tp tr md -> vm_reserved (m_vmmaps md) = segments_reserved segs;
  kd2_noacc : forall G rho tp tr md a n x, K G rho tp tr md -> In (a, n) (vm_noaccess (m_vmmaps md)) ->
      bv_unsigned a <= x < bv_unsigned a + bv_unsigned n ->
      exists b m, In (b, m) (vm_maps (m_vmmaps md)) /\ bv_unsigned b <= x < bv_unsigned b + bv_unsigned m;

  kd2_place : forall G rho tp tr md L, K G rho tp tr md -> depot_inv segs G rho md tp -> dN G <= DNMAX -> (L = NBSZ \/ L = FBSZ) ->
      exists a : word, mmap_place_ok_none (Z_to_bv 64 0) md (Z_to_bv 64 L) a
}.

End WithSegs.
