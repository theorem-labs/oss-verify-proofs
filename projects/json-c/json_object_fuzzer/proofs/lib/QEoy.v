(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8zf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8zf.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= Q6q3.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= Q6q3.mkr__nia_1. Open Scope Z_scope.

Section ST. Variables (sec : Z) (resv : list (Z * Z)) (mb grp : Z).
Definition ST0_B_ctx : mctx := {| c_secret := sec; c_init_done := 1; c_mmap_counter := 1; c_free_meta_head := None; c_avail_meta := Some (0%N, 4280); c_avail_meta_count := 97; c_avail_meta_area_count := 0; c_meta_alloc_shift := 1; c_meta_area_head := Some (0%N, 4096); c_meta_area_tail := Some (0%N, 4096); c_avail_meta_areas := Some (0%N, 8192); c_active := (list_to_map [(23, (0%N, 4240)); (15, (0%N, 4160)); (19, (0%N, 4200)); (2, (0%N, 4120))] : gmap Z aptr); c_usage := (list_to_map [(23, 2); (15, 2); (19, 2); (2, 10)] : gmap Z Z); c_unmap_seq := (list_to_map (@nil (Z*Z)) : gmap Z Z); c_bounces := (list_to_map (@nil (Z*Z)) : gmap Z Z); c_seq := 1; c_brk := BrkDead |}.
Definition ST0_B_regions : gmap N region := list_to_map [(1%N, {| r_kind := RKGroup; r_base := grp; r_len := 4096 |}); (0%N, {| r_kind := RKMeta; r_base := mb; r_len := 8192 |})].
Definition ST0_B_metas : gmap aptr meta := list_to_map [(0%N, 4120, {| m_prev := Some (0%N, 4120); m_next := Some (0%N, 4120); m_mem := Some (1%N, 48); m_avail := 1022; m_freed := 0; m_last_idx := 9; m_freeable := 1; m_sizeclass := 2; m_maplen := 0 |}); (0%N, 4200, {| m_prev := Some (0%N, 4200); m_next := Some (0%N, 4200); m_mem := Some (1%N, 16); m_avail := 2; m_freed := 0; m_last_idx := 1; m_freeable := 1; m_sizeclass := 19; m_maplen := 0 |}); (0%N, 4240, {| m_prev := Some (0%N, 4240); m_next := Some (0%N, 4240); m_mem := Some (1%N, 0); m_avail := 2; m_freed := 0; m_last_idx := 1; m_freeable := 1; m_sizeclass := 23; m_maplen := 1 |}); (0%N, 4160, {| m_prev := Some (0%N, 4160); m_next := Some (0%N, 4160); m_mem := Some (1%N, 32); m_avail := 2; m_freed := 0; m_last_idx := 1; m_freeable := 1; m_sizeclass := 15; m_maplen := 0 |})].
Definition ST0_B_areas : gmap aptr area := list_to_map [(0%N, 4096, {| a_check := sec; a_next := None; a_nslots := 101 |})].
Definition ST0_B_groups : gmap aptr ghdr := list_to_map [(1%N, 0, {| g_meta := Some (0%N, 4240); g_active_idx := 1 |}); (1%N, 48, {| g_meta := Some (0%N, 4120); g_active_idx := 9 |}); (1%N, 32, {| g_meta := Some (0%N, 4160); g_active_idx := 1 |}); (1%N, 16, {| g_meta := Some (0%N, 4200); g_active_idx := 1 |})].
Definition ST0_B_slots : gmap aptr (aptr * Z) := list_to_map [(1%N, 496, (0%N, 4120, 9)); (1%N, 304, (0%N, 4120, 5)); (1%N, 112, (0%N, 4120, 1)); (1%N, 208, (0%N, 4120, 3)); (1%N, 400, (0%N, 4120, 7)); (1%N, 1040, (0%N, 4200, 1)); ( 1%N, 48, (0%N, 4160, 0)); (1%N, 352, (0%N, 4120, 6)); (1%N, 544, (0%N, 4160, 1)); (1%N, 160, (0%N, 4120, 2)); (1%N, 448, (0%N, 4120, 8)); (1%N, 2048, (0%N, 4240, 1)); (1%N, 256, (0%N, 4120, 4)); (1%N, 64, (0%N, 4120, 0)); (1%N, 32, (0%N, 4200, 0)); (1%N, 16, (0%N, 4240, 0))].
Definition ST0_B_shadow_l : list (N * (list (Z * (Z * N)) * list (Z * list (Z * N)) * list (Z * N))) := [(1%N, ([(63, (0, 1%N)); (47, (0, 1%N)); (31, (0, 1%N)); (15, (0, 1%N)); (61, (128, 1%N)); (45, (192, 1%N)); (29, (192, 1%N)); (13, (192, 1%N)); (62, (0, 1%N)); (46, (0, 1%N)); ( 30, (0, 1%N)); (14, (0, 1%N)); (2044, (0, 1%N)); (252, (0, 1%N)); (444, (0, 1%N)); (348, (0, 1%N)); (540, (0, 1%N)); (156, (0, 1%N)); (60, (0, 1%N)); (492, (0, 1%N)); ( 300, (0, 1%N)); (108, (0, 1%N)); (204, (0, 1%N)); (396, (0, 1%N)); (1036, (0, 1%N)); (44, (0, 1%N)); (28, (0, 1%N)); (104, (0, 1%N))], [(5, [(16, 1%N)]); (3, [(12, 1%N)]); (6, [(8, 1%N)]); (4, [(16, 1%N)]); (2, [(12, 1%N)]); (1, [(12, 1%N)]); (0, [(12, 1%N)])], []))].
Definition ST0_B_shadow : gmap N shadow := list_to_map (map (fun kv => (fst kv, mkShadow (list_to_map (fst (fst (snd kv)))) (list_to_map (snd (fst (snd kv)))) (list_to_map (snd (snd kv))))) ST0_B_shadow_l).
Definition ST0_B : mstate := mkState ST0_B_ctx ST0_B_regions ST0_B_shadow 2%N ST0_B_metas ST0_B_areas ST0_B_groups ST0_B_slots 1%N sec resv.
End ST.

Section B. Context {RC__ : RunConsts}.
Variables (sec : Z) (resv : list (Z * Z)) (a1 a2 a3 a4 a5 : Z).
Hypothesis H1 : brk0_answer_ok a1 = true.
Hypothesis Hb : round_up_pg a1 = a1.
Hypothesis H2 : brk_answer_ok a1 (a1 + 2 * PGSZ) a2 = true.
Hypothesis H3 : (a2 =? a1 + 2 * PGSZ) = false.
Hypothesis H4 : mmap_answer_ok (resv ++ []) (2 * PGSZ) a3 = true.
Hypothesis H5 : is_err a3 = false.
Hypothesis H6 : mprotect_answer_ok a4 = true.
Hypothesis H7 : ((a4 =? 0) || (a4 =? TWO64 - ENOSYS)) = true.
Hypothesis H8 : mmap_answer_ok (resv ++ [(a3, 8192)]) 4096 a5 = true.
Hypothesis H9 : is_err a5 = false.

Lemma run_B_gen : follow (mrun o0 (malloc (minit sec resv) 40)) [a1; a2; a3; a4; a5] = Some (o0, (ST0_B sec resv a3 a5, Some (1%N, 64))).
Proof using H1 Hb H2 H3 H4 H5 H6 H7 H8 H9.
unfold mrun, prun.
mgo. mchk H1. rewrite Hb.
mgo. mchk H2.
mgo. mchk H3.
mgo. mchk H4.
mgo. mchk H5.
mgo. mchk H6.
mgo. mchk H7.
mgo. mchk H8.
mgo. mchk H9.
mgo.
lazymatch goal with |- follow (eruns ?s ?u ?o (SRet ?x)) [] = ?r => let x' := flat x in change_no_check (Some (o, x') = r) end.
reflexivity.
Qed.
End B.

Theorem startup_malloc40_mmap {RC__ : RunConsts} (sec : Z) (resv : list (Z * Z)) (brk0 mb grp : Z) :
brk0_answer_ok brk0 = true ->
mmap_answer_ok (resv ++ []) (2 * PGSZ) mb = true ->
is_err mb = false ->
mmap_answer_ok (resv ++ [(mb, 8192)]) 4096 grp = true ->
is_err grp = false ->
follow (mrun o0 (malloc (minit sec resv) 40)) [brk0; brk0; mb; 0; grp] = Some (o0, (ST0_B sec resv mb grp, Some (1%N, 64))).
Proof.
intros H1 H4 H5 H8 H9.
apply run_B_gen; try assumption; try reflexivity.
- unfold brk0_answer_ok in H1. apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [H1a H1b].
apply round_up_pg_aligned; [apply Z.ltb_lt in H1a; lia | apply Z.eqb_eq in H1b; exact H1b].
- unfold brk_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
- apply Z.eqb_neq. unfold PGSZ. lia.
Qed.
