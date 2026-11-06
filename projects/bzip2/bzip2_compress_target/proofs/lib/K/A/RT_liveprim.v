(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require BackingAlgebra.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_cache_defs R_prim_defs R_depot_defs R_fs_defs R_glue_defs R_m2s R_poison RT_state RT_rep RT_facts0.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition af_live_primary (RT : rt_sig) : Prop :=
  forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p.

Lemma rta_live_primary : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> n <= 64512 -> SEGTOP_A <= p.
Proof.
  intros Σ m p n H Hin Hn. pose proof (ART_wf Σ m H) as (HL & HR & HV & HS & _).
  destruct HV as (_ & _ & HVin & _).
  destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _). unfold l_ACEIL in P3.
  unfold SEGTOP_A, STACK_WIN, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  destruct (HVin p n Hin) as [(c & i & Hc & Hn' & ->)|(s & Hs & Hq & <- & ->)].
  - destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _).
    pose proof (nth_error_In _ _ Hn') as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (ClassSize_pos c Hc) as Hcs. unfold p_ubeg, p_abeg, kUserCap in *.
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 0 < rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    lia.
  - exfalso. destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & _). lia.
Qed.

Theorem rta_live_primary_af : af_live_primary RTA.
Proof. intros Σ m p n HA Hin Hn. exact (rta_live_primary Σ m p n HA Hin Hn). Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require BackingAlgebra.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_sizeclass R_cache_defs R_prim_defs R_depot_defs R_fs_defs
  R_glue_defs R_m2s R_poison RT_state RT_rep RT_facts0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition af_live_primary (RT : rt_sig) : Prop :=
  forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p.

Lemma rta_live_primary : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> n <= 64512 -> SEGTOP_A <= p.
Proof.
  intros Σ m p n H Hin Hn. pose proof (ART_wf Σ m H) as (HL & HR & HV & HS & _).
  destruct HV as (_ & _ & HVin & _).
  destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _). unfold l_ACEIL in P3.
  unfold SEGTOP_A, STACK_WIN, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *.
  destruct (HVin p n Hin) as [(c & i & Hc & Hn' & ->)|(s & Hs & Hq & <- & ->)].
  - destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & _).
    pose proof (nth_error_In _ _ Hn') as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (ClassSize_pos c Hc) as Hcs. unfold p_ubeg, p_abeg, kUserCap in *.
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 0 < rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    lia.
  - exfalso. destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & _). lia.
Qed.

Theorem rta_live_primary_af : af_live_primary RTA.
Proof. intros Σ m p n HA Hin Hn. exact (rta_live_primary Σ m p n HA Hin Hn). Qed.
