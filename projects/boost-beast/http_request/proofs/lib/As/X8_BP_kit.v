(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Lemma shvis_transport_fr : forall W m m' lo hi ff k sa shc,
  shvis m lo hi -> munch W m m' -> wmono asegs m m' ->
  rw_cells asegs m' sa shc -> sa = sh ff -> Z.of_nat (cells_size shc) = k ->
  Forall (win_fr ff k) W -> 0 <= lo <= hi -> hi <= AAPP_HI ->
  shvis m' lo hi.
Proof.
  intros W m m' lo hi ff k sa shc SV MU WM SHC -> SZ FW LH HH'.
  eapply shvis_transport_cov; [exact SV| exact MU| exact WM| exact SHC|]. rewrite SZ.
  pose proof (sh_hull_range lo hi LH HH') as (Q1 & Q2 & _ & _).
  intros x Hx.
  destruct (Z.lt_ge_cases x (sh ff)) as [X1|X0]; [left| destruct (Z.lt_ge_cases x (sh ff + k)) as [X2|X1]; [right; clear - X0 X2; lia| left]].
  all: clear MU WM SHC SV; induction W as [|[l h] W IH]; cbn; [exact I|];
       pose proof (Forall_inv FW) as K; unfold win_fr in K; cbn [fst snd] in K;
       split; [clear IH; unfold AHI_LO, ALOWSH_LO in *; lia| apply IH; exact (Forall_inv_tail FW)].
Qed.

(* [comment removed for export] *)
Lemma land1_odd : forall lc, 0 <= lc -> Z.odd lc = true -> Z.land lc 1 = 1.
Proof.
  intros lc H Ho. rewrite Z.land_ones with (n := 1) by lia. change (2^1) with 2.
  rewrite Zmod_odd. rewrite Ho. reflexivity.
Qed.
Lemma land1_even : forall lc, 0 <= lc -> Z.odd lc = false -> Z.land lc 1 = 0.
Proof.
  intros lc H Ho. rewrite Z.land_ones with (n := 1) by lia. change (2^1) with 2.
  rewrite Zmod_odd. rewrite Ho. reflexivity.
Qed.

Lemma zeros24_ec : forall m E, rw_cells asegs m E [CB 24 (poison_bytes 24 0)] -> rw_cells asegs m E (ErrCodeCells EC_clear).
Proof.
  intros m E V. unfold ErrCodeCells, EC_clear. cbn [ec_val ec_cat ec_flags].
  eapply rw_cells_reshape; [exact V| cbn; repeat split; reflexivity| vm_compute; reflexivity].
Qed.

Lemma ec_CB24 : forall m E Ev, rw_cells asegs m E (ErrCodeCells Ev) -> exists ej, rw_cells asegs m E [CB 24 ej].
Proof.
  intros m E Ev C. destruct (rw_cells_forget _ _ _ _ C) as [ej C']. exists ej. cbn [cells_size csize Nat.add ErrCodeCells] in C'. exact C'.
Qed.

End HCW.
