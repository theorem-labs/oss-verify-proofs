(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RRealloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require RF_malloc_spec RF_realloc_spec.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg LibOps ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit Driver_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import InitMem.
From OSSVerify.Proofs.openssl.bndiv.lib.HX Require Import HxVal HxMem HxStep HxHook.
From OSSVerify.Proofs.openssl.bndiv.lib.HXU Require Import HxuInit HxuInv HxuMain HxuFinal HxuLaws.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel. (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnRep.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

#[export] Instance LSP_bndiv : LibSpec :=
  {| lib_pristine := hx_pristine; lib_inv := lib_inv_bn; LIBW := LIBW_HX; LIB_STACK := 65536 |}.

(* [comment removed for export] *)
Lemma ops_model : map dec_op OPS = bndiv_ops.
Proof. vm_compute. reflexivity. Qed.

Lemma LL_bndiv : LibLaws.
Proof.
  constructor.
  - exact LIBW_HX_img.
  - cbn. lia.
  - cbn. lia.
  - (* [comment removed for export] *)
    intros m Hnone (T1 & T2). split; [exact Hnone|]. split; [exact T1|].
    eapply rw_cells_recast; [exact T2 | cbn; auto | vm_compute; reflexivity | reflexivity].
  - (* [comment removed for export] *)
    intros m m' (H1 & H2 & H3) AG. split; [|split].
    + intros a Ha Hi Hn. rewrite (proj1 (AG a Ha Hi)). exact (H1 a Ha Hi Hn).
    + eapply rw_cells_agree; [exact AG | exact H2 |]. intros a Ha. cbn [cells_size csize Nat.add Z.of_nat] in Ha. cbn [LIBW LSP_bndiv rin_ivs LIBW_HX fst snd]. lia.
    + eapply rw_cells_agree; [exact AG | exact H3 |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [LIBW LSP_bndiv rin_ivs LIBW_HX fst snd]. lia.
  - (* [comment removed for export] *)
    intros ls OW m m' HI AG. exact (lib_inv_bn_agree ls OW m m' HI AG).
Qed.

(* [comment removed for export] *)
Theorem rinit_bndiv : rinit_stmt.
Proof.
  apply (hx_rinit_bn (LM := LM_bndiv) (LSP := LSP_bndiv) RF_malloc_spec.rmalloc_spec RF_realloc_spec.rrealloc_spec (ls_init : @LS LM_bndiv)).
  - unfold lib_init, LM_bndiv. rewrite ops_model. reflexivity.
  - reflexivity.
  - cbn. lia.
  - intros m H. exact H.
  - intros m OW H. exact (lib_inv_init m OW H).
Qed.

End WithCeiling0.
