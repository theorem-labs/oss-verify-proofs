(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_depot_defs R_unwind_defs R_unwind_chain RT_state.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MAIN_PCS : list Z := [PC_MALLOC; PC_FREE].

Lemma T_MAIN_eq : T_MAIN = traces_of MAIN_PCS SITE_TRACES. Proof. reflexivity. Qed.

Lemma sites_ok : sites_okb 4096 MAIN_PCS 4 SITE_TRACES = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma T_MAIN_rng64 : forall tr, In tr T_MAIN -> Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
  intros tr H. assert (X : forallb (fun t => forallb (fun x => (0 <=? x) && (x <? 2 ^ 64)) t) T_MAIN = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X tr H) as Y. cbv beta in Y. apply Forall_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) Y x Hx) as Z0. cbv beta in Z0. apply andb_prop in Z0 as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. lia.
Qed.

(* [comment removed for export] *)
Theorem site_trace_main : forall (m : mem) pc bot top (ra s0 sp : word),
  In pc MAIN_PCS -> unwind_ch m ra s0 sp -> top - 16 <= 2 ^ 63 ->
  exists ch tr, chain_cells [(0, bv_unsigned sp)] m (bv_unsigned s0) ch
    /\ unwind_trace pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr
    /\ In tr T_MAIN /\ (1 <= length tr <= 5)%nat.
Proof.
  intros m pc bot top ra s0 sp Hpc (ras & Hs & HU) Htop.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  destruct (site_unwind USTACK_TOP [(0, bv_unsigned sp)] m MAIN_PCS SITE_TRACES 4 pc bot top 30 (bv_unsigned sp) (bv_unsigned ra)
              (bv_unsigned s0) ras sites_ok Hpc Hs ltac:(unfold USTACK_TOP; lia) Htop ltac:(lia) ltac:(cbn; lia) HU)
    as (ch & tr & CC & ET & HT & HL).
  { intros a Ha _. cbn [disjoint_from]. split; [right; exact Ha | exact I]. }
  exists ch, tr. split; [exact CC|]. split; [exact ET|]. split; [rewrite T_MAIN_eq; exact HT | cbn in HL; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_depot_defs R_unwind_defs R_unwind_chain RT_state.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition MAIN_PCS : list Z := [PC_MALLOC; PC_FREE].

Lemma T_MAIN_eq : T_MAIN = traces_of MAIN_PCS SITE_TRACES. Proof. reflexivity. Qed.

Lemma sites_ok : sites_okb 4096 MAIN_PCS 4 SITE_TRACES = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma T_MAIN_rng64 : forall tr, In tr T_MAIN -> Forall (fun x => 0 <= x < 2 ^ 64) tr.
Proof.
  intros tr H. assert (X : forallb (fun t => forallb (fun x => (0 <=? x) && (x <? 2 ^ 64)) t) T_MAIN = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) X tr H) as Y. cbv beta in Y. apply Forall_forall. intros x Hx.
  pose proof (proj1 (forallb_forall _ _) Y x Hx) as Z0. cbv beta in Z0. apply andb_prop in Z0 as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2. lia.
Qed.

(* [comment removed for export] *)
Theorem site_trace_main : forall (m : mem) pc bot top (ra s0 sp : word),
  In pc MAIN_PCS -> unwind_ch m ra s0 sp -> top - 16 <= 2 ^ 63 ->
  exists ch tr, chain_cells [(0, bv_unsigned sp)] m (bv_unsigned s0) ch
    /\ unwind_trace pc 4096 bot top 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr
    /\ In tr T_MAIN /\ (1 <= length tr <= 5)%nat.
Proof.
  intros m pc bot top ra s0 sp Hpc (ras & Hs & HU) Htop.
  pose proof (bv_unsigned_in_range 64 sp) as RSP.
  destruct (site_unwind USTACK_TOP [(0, bv_unsigned sp)] m MAIN_PCS SITE_TRACES 4 pc bot top 30 (bv_unsigned sp) (bv_unsigned ra)
              (bv_unsigned s0) ras sites_ok Hpc Hs ltac:(unfold USTACK_TOP; lia) Htop ltac:(lia) ltac:(cbn; lia) HU)
    as (ch & tr & CC & ET & HT & HL).
  { intros a Ha _. cbn [disjoint_from]. split; [right; exact Ha | exact I]. }
  exists ch, tr. split; [exact CC|]. split; [exact ET|]. split; [rewrite T_MAIN_eq; exact HT | cbn in HL; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
