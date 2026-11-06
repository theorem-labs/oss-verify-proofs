(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs R_quar_defs R_deallocate R_qput R_qenqueue R_asan_free R_prim_kit R_depot_unwind RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malpre RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freeC RT_freeD.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_leaves.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_sec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_quar_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_deallocate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qput.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qenqueue.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_asan_free.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_unwind.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_frame.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_trans.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malpre.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malstate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freelift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_geo0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_fkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeA2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeC.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeD.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma artm_eq : forall Σ Σ' mo, lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ' = rt_eager Σ -> ARTM_A Σ mo -> ARTM_A Σ' mo.
Proof.
  intros Σ Σ' mo E1 E2 E3 (A1 & A2 & A3 & A4 & AS).
  unfold ARTM_A, artm_sys, confined0, rt_maps in *. rewrite E1, E2, E3. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  exact AS.
Qed.

Lemma rt_eager_fp : forall Σ c i n p D' l, 1 <= c <= 31 -> rt_eager (set_ql (free_p Σ c i n p D') l) = rt_eager Σ.
Proof.
  intros Σ c i n p D' l Hc. unfold rt_eager, set_ql, free_p. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
  destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; unfold upd_reg; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma fe_dep : forall Σ m tr, ART_A Σ m -> (In tr T_MAIN /\ (1 <= length tr <= 5)%nat) ->
  depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)) /\ dep_inv (fst (depot_put (dep Σ) tr)).
Proof.
  intros Σ m tr HA Htr. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
  assert (TRM : In tr T_MAIN /\ (length tr <= 5)%nat) by (destruct Htr as (H1 & H2); split; [exact H1 | lia]).
  destruct TRM as (TRM & TRL).
  split; [apply (qc_depot_ok_put_ok _ _ _ _ _ DOK DN); lia | exact (dep_inv_put _ _ DINV TRM ltac:(lia))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs
  R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_unwind_defs
  R_quar_defs R_deallocate R_qput R_qenqueue R_asan_free R_prim_kit R_depot_unwind
  RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malpre RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2
  RT_freeC RT_freeD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma artm_eq : forall Σ Σ' mo, lay Σ' = lay Σ -> sec Σ' = sec Σ -> rt_eager Σ' = rt_eager Σ -> ARTM_A Σ mo -> ARTM_A Σ' mo.
Proof.
  intros Σ Σ' mo E1 E2 E3 (A1 & A2 & A3 & A4 & AS).
  unfold ARTM_A, artm_sys, confined0, rt_maps in *. rewrite E1, E2, E3. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  exact AS.
Qed.

Lemma rt_eager_fp : forall Σ c i n p D' l, 1 <= c <= 31 -> rt_eager (set_ql (free_p Σ c i n p D') l) = rt_eager Σ.
Proof.
  intros Σ c i n p D' l Hc. unfold rt_eager, set_ql, free_p. cbn [pr sec sec_nres]. f_equal. f_equal. apply sum_cls_ext. intros k _.
  destruct (Z.eqb_spec (Z.of_nat k) c) as [Ek|Ek]; [rewrite Ek; unfold upd_reg; reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma fe_dep : forall Σ m tr, ART_A Σ m -> (In tr T_MAIN /\ (1 <= length tr <= 5)%nat) ->
  depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)) /\ dep_inv (fst (depot_put (dep Σ) tr)).
Proof.
  intros Σ m tr HA Htr. pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & DOK & DN & DT & DINV & _).
  assert (TRM : In tr T_MAIN /\ (length tr <= 5)%nat) by (destruct Htr as (H1 & H2); split; [exact H1 | lia]).
  destruct TRM as (TRM & TRL).
  split; [apply (qc_depot_ok_put_ok _ _ _ _ _ DOK DN); lia | exact (dep_inv_put _ _ DINV TRM ltac:(lia))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
