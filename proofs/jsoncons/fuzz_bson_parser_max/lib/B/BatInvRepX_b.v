(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk HeapIface HeapIfaceA HeapIfaceABx As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFxQ_b BatInvFreePure_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).

Section X.
Variable FSG : Type.
Definition art_rt_quar_x (bt bg : Z) (rn : art_run) (G : art_gs FSG) (M : word -> option byte) : Prop :=
  (exists f l, cellA M (rn_t rn + 80) 8 (Z.of_nat (length (g_qt FSG G))) /\ cellA M (rn_t rn + 88) 8 f /\ cellA M (rn_t rn + 96) 8 l
               /\ cellA M (rn_t rn + 104) 8 (art_batches_bytes (g_qt FSG G)) /\ art_batch_list M (g_qt FSG G) f l)
  /\ (exists f l, cellA M (0x13c8b0 + 160) 8 (Z.of_nat (length (g_qg FSG G))) /\ cellA M (0x13c8b0 + 168) 8 f /\ cellA M (0x13c8b0 + 176) 8 l
               /\ cellA M (0x13c8b0 + 184) 8 (art_batches_bytes (g_qg FSG G)) /\ art_batch_list M (g_qg FSG G) f l)
  /\ art_batches_bytes (g_qt FSG G) <= bt /\ art_batches_bytes (g_qg FSG G) <= bg
  /\ cellA M (0x13c8b0 + 152) 4 0
  /\ NoDup (map bt_addr (g_qt FSG G ++ g_qg FSG G))
  /\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) -> bt_items b <> [])
  /\ (forall b it, In b (g_qt FSG G ++ g_qg FSG G) -> In it (bt_items b) ->
        (exists c w, 1 <= c <= 30 /\ art_cptr_ok (AsanTab.class_size c) (cl_au (g_cls FSG G c)) w /\ g_st FSG G c w = CQuar (fst it + 16) (snd it))
        \/ (exists s, In s (g_sec FSG G) /\ sc_quar s = true /\ sc_u s = fst it + 16 /\ sc_n s = snd it))
  /\ NoDup (map fst (flat_map bt_items (g_qt FSG G ++ g_qg FSG G)))
  /\ (forall b, In b (g_qt FSG G ++ g_qg FSG G) ->
        exists w, bt_addr b = rn_spb rn + 24 * 2 ^ 32 + 16 * w /\ art_cptr_ok (AsanTab.class_size 24) (cl_au (g_cls FSG G 24)) w /\ g_st FSG G 24 w = CBatch).
Definition art_alloc_rep_x (bt bg : Z) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte) : Prop :=
  art_run_ok rn /\ art_rt_statics rn M /\ art_rt_thread rn M /\ art_rt_primary FSG rn G M /\ art_rt_chunks FSG rn G LB M
  /\ art_rt_sec FSG rn G LB M /\ art_rt_quar_x bt bg rn G M /\ art_rt_depot FSG rn G M /\ art_rt_ia FSG G M /\ art_rt_blocks FSG rn G LB
  /\ art_rt_ghost FSG rn G M.

#[using="Type"] Lemma art_alloc_rep_x_b : forall b rn G LB M, art_alloc_rep_x b (2 ^ 28) rn G LB M = art_alloc_rep_b FSG b rn G LB M.
Proof. reflexivity. Qed.
#[using="Type"] Lemma art_alloc_rep_x_closed : forall rn G LB M, art_alloc_rep_x (2 ^ 20) (2 ^ 28) rn G LB M = art_alloc_rep FSG rn G LB M.
Proof. reflexivity. Qed.

End X.
