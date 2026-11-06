(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "or"; "eq"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "mul"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "sc_map_beg"; "aa_geom"; "aa_sec"; "sc_map_size"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_cache_inited"; "aa_cls"; "aa_depot"; "aa_fs_busy"; "aa_fs_hint"; "aa_internal_inited"; "aa_live"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "ag_pab"; "mkAA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@Corelib.Init.Datatypes"; "Some"; "length"; "option"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "set_sec"; "swap_remove"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import BackingAlgebra Virt SoundA SummaryA MmapFixedA MadviseSpecA MadviseA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv SegQ_defs SegQ_wf2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition swap_remove {T} (l : list T) (i : nat) : list T :=
  match nth_error l (length l - 1) with
  | Some x => if Nat.eqb i (length l - 1) then removelast l else list_upd (removelast l) i x
  | None => l
  end.
Definition set_sec (A : AA) (s : list sec_chunk) : AA := ltac2:(tb__ "0|0|
S1cSbVA;A1S12VA;A1S11VA;A1Vs;S18VA;A1S17VA;A1S1aVA;A1S19VA;A1S13VA;A1S15VA;A1S14VA;A1S16VA;A1S10VA;A1SfVA;A1SeVA;A1Af").
Definition unmap_sec (A : AA) (i : nat) : AA := ltac2:(tb__ "0|0|
S23VA;S24S9ScVA;A1Vi;A3A2").

Definition sec_junk_zone (z : Z) : Prop := ltac2:(tb__ "0|0|
S1S0S5S4S1dZ40A2Vz;A2S6Vz;Zead00A2A2S0S5Zead08Vz;A2S6Vz;Zead30A2A2A2").

Definition sec_tbl_zone (A : AA) (i : nat) (z : Z) : Prop := ltac2:(tb__ "0|4|
S1S0S5S4S1dZ38A2Vz;A2S6Vz;S4S1dZ40A2A2A2S1S0S5Zead00Vz;A2S6Vz;Zead04A2A2S1S0S5S4S1bSbVA;A1A1S7Z8M0S8Vi;A1A2A2M1Vz;A2S6Vz;S4G1G0A2A2A2S3S9S9S0S2S21S9A1S25S9ScVA;A1M2S22S20S9G2A2U1A2A3S1fS9R1A2A3S0S5S4SaR1A1M3Z18A2Vz;A2S6Vz;S4G3Z20A2A2A2A2Llst;A2A2A2A2").
Definition chunk_zone (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|1|
S0S5SaVch;A1M0Vz;A2S6Vz;S4G0SdVch;A1A2A2A2").
Definition chunk_sh_zone (ch : sec_chunk) (z : Z) : Prop := ltac2:(tb__ "0|1|
S0S5S1eSaVch;A1M0A1Vz;A2S6Vz;S1eS4G0SdVch;A1A2A1A2A2").

Section WithSegs.
Variable segs : list Segment.

Record KQ_sec (K : AA -> jpredA) : Prop := mkKQS {

  ks_repr : forall A rho tp tr md, K A rho tp tr md -> secondary_repr (view segs (rm rho)) A;

  ks_item : forall A rho tp tr md, K A rho tp tr md -> forall it, In it (qitems (qall A)) -> is_primary (snd it) = false ->
      exists i ch, nth_error (aa_sec A) i = Some ch /\ fst it = sc_map_beg ch + PG + 2048 /\ sc_size ch = round_up (snd it) 8 + 4096;

  ks_sep : forall A rho tp tr md, K A rho tp tr md -> forall i ch, nth_error (aa_sec A) i = Some ch ->
      let G := aa_geom A in
      (sc_map_beg ch + sc_map_size ch <= ag_spacebeg G \/ ag_spacebeg G + kSpaceSize + 4096 <= sc_map_beg ch)
      /\ (sc_map_beg ch + sc_map_size ch <= ag_thread G \/ ag_thread G + 0x1000 <= sc_map_beg ch)
      /\ (sc_map_beg ch + sc_map_size ch <= ag_pab G \/ ag_pab G + kPtrArrayReserve <= sc_map_beg ch)
      /\ (sc_map_beg ch + sc_map_size ch <= ag_ctx G \/ ag_ctx G + 0x1000 <= sc_map_beg ch)
      /\ (forall j ch', nth_error (aa_sec A) j = Some ch' -> i <> j ->
            sc_map_beg ch + sc_map_size ch <= sc_map_beg ch' \/ sc_map_beg ch' + sc_map_size ch' <= sc_map_beg ch);

  ks_nodup : forall A rho tp tr md, K A rho tp tr md ->
      NoDup (List.map fst (List.filter (fun it : Z * Z => negb (is_primary (snd it))) (qitems (qall A))));

  ks_munmap_ok : forall A rho tp tr md, K A rho tp tr md -> forall ch, In ch (aa_sec A) ->
      let a := Z_to_bv 64 (sc_map_beg ch) in let n := Z_to_bv 64 (sc_map_size ch) in
      map_has (vm_maps (m_vmmaps md)) a n = true
      /\ (forall s, In (a, s) (vm_maps (m_vmmaps md)) -> s = n)
      /\ region_free (map_remove (vm_maps (m_vmmaps md)) a) a n = true;

  ks_madvise_ok : forall A rho tp tr md, K A rho tp tr md -> forall (a : word) (n : Z),
      bv_unsigned a mod PG = 0 -> n mod PG = 0 -> 0 < n ->
      ((LOW_SHADOW_BEG <= bv_unsigned a /\ bv_unsigned a + n <= SHADOW_GAP_BEG) \/ (HIGH_SHADOW_BEG <= bv_unsigned a /\ bv_unsigned a + n <= HIGH_SHADOW_END)) ->
      madvise_dontneed_ok (m_vmmaps md) a (Z_to_bv 64 n) = true
      /\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + n -> page_in_ranges (page_base x) (m_vm_lazy md) = true);

  kq_secshadow : forall A rho rho' tp tr md it i ch,
      In it (qitems (qall A)) -> is_primary (snd it) = false -> nth_error (aa_sec A) i = Some ch -> fst it = sc_map_beg ch + PG + 2048 ->
      (forall i0, rw rho' i0 = rw rho i0) -> (forall l, rl rho' l = rl rho l) ->
      (forall z, ~ QW A z -> ~ chunk_sh_zone ch z -> view segs (rm rho') z = view segs (rm rho) z) ->
      (forall z, QW A z \/ chunk_sh_zone ch z -> view segs (rm rho) z <> None -> view segs (rm rho') z <> None) ->
      K A rho tp tr md -> K A rho' tp tr md;

  kq_unmap : forall A rho rho' tp tr md g1 g2 a it i2 s s' i ch,
      aa_q_thread A = [] -> aa_q_global A = g1 ++ mkQB a (it :: i2) s :: g2 -> is_primary (snd it) = false ->
      nth_error (aa_sec A) i = Some ch -> fst it = sc_map_beg ch + PG + 2048 ->
      let G := aa_geom A in let n := Z.of_nat (length (aa_sec A)) in
      (forall i0, rw rho' i0 = rw rho i0) -> (forall l, rl rho' l = rl rho l) ->
      (forall z, ~ QW A z -> ~ sec_junk_zone z -> ~ sec_tbl_zone A i z -> ~ chunk_zone ch z -> ~ chunk_sh_zone ch z ->
                 view segs (rm rho') z = view segs (rm rho) z) ->
      (forall z, QW A z \/ sec_junk_zone z \/ chunk_sh_zone ch z -> view segs (rm rho) z <> None -> view segs (rm rho') z <> None) ->
      cell_ok (view segs (rm rho')) (mkACell (SEC_INST + 56) 8 (n - 1)) ->
      cell_ok (view segs (rm rho')) (mkACell 0xead00 4 0) ->
      (forall lst, nth_error (aa_sec A) (length (aa_sec A) - 1) = Some lst ->
         (Z.of_nat i < n - 1 -> cell_ok (view segs (rm rho')) (mkACell (ag_pab G + 8 * Z.of_nat i) 8 (sc_map_beg lst))
                                /\ cell_ok (view segs (rm rho')) (mkACell (sc_map_beg lst + 24) 8 (Z.of_nat i)))
         /\ (Z.of_nat i = n - 1 -> forall z, ag_pab G + 8 * Z.of_nat i <= z < ag_pab G + 8 * Z.of_nat i + 8 -> view segs (rm rho') z = view segs (rm rho) z)) ->

      paid (munmap_model md (Z_to_bv 64 (sc_map_beg ch)) (Z_to_bv 64 (sc_map_size ch)))
           (tp_forget (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) tp) <= paid md tp ->
      K A rho tp tr md ->
      K (unmap_sec (set_q A [] (g1 ++ mkQB a i2 s' :: g2)) i) rho'
        (tp_forget (sc_map_beg ch) (sc_map_beg ch + sc_map_size ch) tp) tr
        (munmap_model md (Z_to_bv 64 (sc_map_beg ch)) (Z_to_bv 64 (sc_map_size ch)))
}.
End WithSegs.
