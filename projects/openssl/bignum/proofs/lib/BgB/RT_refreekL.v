(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Mem Frame Cells Step Arr Exec RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.AS Require Import AsanAcct.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow R_sizeclass.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeI RT_freeJ RT_freeL RT_refreekA RT_refreekC RT_refreekD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section NewG.
Variables (Σ : rtsA) (c : Z) (i : nat) (n : Z) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf0 Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkQuar n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σ)) 24 j0) (map fst (ql Σ))).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0xFFB0 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Lemma ng_geo_r : geo_ok Σ.
Proof using HW0. exact (geo_of_wf0 Σ HW0). Qed.

Lemma ng_jB_r : nth_error (r_st (pr Σ 24)) jB = Some CkIdle.
Proof using HW0 HCA.
  clear - HW0 HCA. pose proof HW0 as (_ & HR & _). destruct HR as (_ & _ & R3 & _). destruct (R3 24 ltac:(lia)) as (_ & _ & C3).
  rewrite HCA in C3. pose proof (proj1 (Forall_forall _ _) C3 (Z.of_nat jB) ltac:(apply in_or_app; right; left; reflexivity)) as (_ & X).
  rewrite Nat2Z.id in X. exact X.
Qed.

End NewG.
