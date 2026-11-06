(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanhz7 Asanjze.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ARtStmts AInioec AInit0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma wr_at_img : forall (m : mem) a n, 0xa8000 <= a -> a + n <= 0x60a000 -> wr_at rsegs m a n.
Proof.
  intros m a n H1 H2. split; [lia|]. split; [lia|]. intros i Hi. unfold wa. change rsegs with ASEGS.
  apply asan_rw_window. rewrite unsigned_lit by lia. lia.
Qed.
Lemma wr_at_heap : forall (m : mem) a n, mapped m a n -> 0 <= a -> a + n <= 2^64 -> wr_at rsegs m a n.
Proof.
  intros m a n M Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. unfold wview, wa.
  destruct (m (Z_to_bv 64 (a + i))) eqn:E; [discriminate|]. exfalso. exact (M i Hi E).
Qed.
Lemma rw_C4 : forall (m : mem) a v, u32_at rsegs m a v -> wr_at rsegs m a 4 -> rw_cells rsegs m a [C4 (wz v)].
Proof. intros m a v B W. split; [split; [exact (conj I I)| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]| exact W]. Qed.
Lemma ro_C8 : forall (m : mem) a v, u64_at rsegs m a v -> ro_cells rsegs m a [C8 (wz v)].
Proof. intros m a v B. split; [exact (conj I I)| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]. Qed.
Lemma headL_1 : forall k1 b, headL [k1] b = (if Z.eqb b (bkt k1) then 1 else 0).
Proof.
  intros k1 b. unfold headL. cbn [chainL app].
  destruct (Z.eqb_spec (bkt k1) b); destruct (Z.eqb_spec b (bkt k1)); cbn; lia.
Qed.
Lemma depot_total_1 : forall k1, depot_total [k1] = 1 + Z.of_nat (length k1).
Proof. intros. unfold depot_total, depot_off. cbn. lia. Qed.

Section L.
  Context {Clg : Ceiling}.
  Theorem depot_init_okL : depot_init_ok2 (DR:=DepotRepL).
  Proof.
    intros P k1 sp0 FULL md m RAW D. cbn [depot_rep DepotRepL].
    destruct D as [K TAB NU M0 MJ N1 NZ SST SSA SSB FR BL]. destruct K as [KL KR]. destruct BL as [Mn Mf].
    pose proof (ar0_place _ _ _ _ _ RAW) as PL. pose proof (ar0_bigmaps _ _ _ _ _ RAW) as [SEP BND].
    apply wf_place_cheap in PL. pose proof alloc_ceiling_val as CE.
    assert (N0 : app_rangeA AL_pasan (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P + kDepotNodesBlock <= alloc_ceiling /\ p_nodes0 P mod 4096 = 0) by tauto.
    assert (F0 : app_rangeA AL_pasan (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P + kStackStoreBlockBytes <= alloc_ceiling /\ p_frames0 P mod 4096 = 0) by tauto.
    clear PL. destruct N0 as (N0a & N0b & N0c). destruct F0 as (F0a & F0b & F0c). apply app_facts in N0a. apply app_facts in F0a.
    cbn [al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore AL_pasan] in *.
    unfold depot_repL. cbn [al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore AL_pasan length Z.of_nat Pos.of_succ_nat].
    unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kDepotNodesL1 in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros b Hb. rewrite headL_1. change (bkt k1) with (depot_bucket k1). apply rw_C4; [exact (TAB b Hb)| apply wr_at_img; lia].
    - apply rw_C4; [exact NU| apply wr_at_img; lia].
    - apply ro_C8. exact M0.
    - intros i Hi. assert (i = 1) by lia. subst i. destruct N1 as (A1 & A2 & A3).
      unfold hshL, linkL, sidL, keyL. change (Z.to_nat (1 - 1)) with 0%nat.
      cbn [take nth headL chainL hd app firstn length]. change (Yr.ADepotM.depot_off [k1] 0 + 1) with 1.
      replace (p_nodes0 P + 16 * 1) with (p_nodes0 P + 16) by lia.
      split; [split; [exact (conj I (conj I (conj I I)))|]|].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact A1|]. rewrite length_le8.
        apply bytes_at_app. split; [replace (p_nodes0 P + 16 + Z.of_nat 8) with (p_nodes0 P + 24) by lia; exact A2|]. rewrite length_le4.
        replace (p_nodes0 P + 16 + Z.of_nat 8 + Z.of_nat 4) with (p_nodes0 P + 28) by lia. exact A3.
      + apply wr_at_heap; [| lia| cbn; lia]. cbn [cells_size csize Nat.add]. intros j Hj. replace (p_nodes0 P + 16 + j) with (p_nodes0 P + (16 + j)) by lia. apply Mn. lia.
    - exists (le8 (wz kStackStoreBlockBytes)), (le4 (wz 0)). destruct SSB as (B1 & B2 & B3).
      split; [split; [cbn [cells_wf cell_wf]; rewrite length_le8, length_le4; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity|]|].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r. change (Yr.ADepotM.depot_total [k1]) with (depot_total [k1]). rewrite depot_total_1.
        apply bytes_at_app. split; [exact SST|]. rewrite length_le8.
        apply bytes_at_app. split; [exact SSA|]. rewrite length_le8.
        apply bytes_at_app. split; [replace (1602184 + Z.of_nat 8 + Z.of_nat 8) with (1602184 + 16) by lia; exact B1|]. rewrite length_le8.
        apply bytes_at_app. split; [replace (1602184 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (1602184 + 24) by lia; exact B2|]. rewrite length_le4.
        replace (1602184 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 4) with (1602184 + 28) by lia. exact B3.
      + apply wr_at_img; cbn; lia.
    - exact Mn.
    - exact Mf.
    - apply (mod0_down _ 4096 16); [exists 256; reflexivity| exact N0c].
    - apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact F0c].
    - (* [comment removed for export] *)
      exact (SEP 7%nat 8%nat _ _ _ _ eq_refl eq_refl ltac:(lia)).
    - change (Yr.ADepotM.depot_total [k1]) with (depot_total [k1]). rewrite depot_total_1. lia.
    - lia.
    - lia.
    - lia.
    - lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End L.
