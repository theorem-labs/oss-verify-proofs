(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OSSVerify.Proofs.openssl.bndiv.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.MallocU Require RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg LibOps ProgG.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnModel BnTree BnInv BnSpecs BnMInv BnBridge.
From OSSVerify.Proofs.openssl.bndiv.lib.U Require Import Layout Lib_iface Lib_kit Driver_iface.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require Import BnHeap BnRep BnIface.
From OSSVerify.Proofs.openssl.bndiv.lib.BnU Require W_div W_bin2bn W_fuzz.
From OSSVerify.Proofs.openssl.bndiv.lib.BnWU Require BnCallsU HxComba8U.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAU Require W_add W_cmp W_mul.
From OSSVerify.Proofs.openssl.bndiv.lib.HXU Require Import HxuInit HxuInst HxuFuzzGap.
From OSSVerify.Proofs.openssl.bndiv.lib.HXP Require Import BndivModel.
From OSSVerify.Proofs.openssl.bndiv.lib.HXU Require HxuCall.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition BN_MUL_STACK_DEBT : Z := W_mul.BN_MUL_STACK.

(* [comment removed for export] *)
Definition BN_mul_walk_stmt : Prop := forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
    (lo B : Z) (errv : word) (rr rx ry : bnref) (ar ax ay : Z),
  bn_pre s ls m OW LB AD EA sp lo B errv BN_MUL_STACK_DEBT -> tp = wz RATP ->
  ref_at ls OW AD rr ar -> ref_at ls OW AD rx ax -> ref_at ls OW AD ry ay ->
  a0 = wz ar -> a1 = wz ax -> a2 = wz ay -> a3 = wz (ad_ctx AD) ->
  W_div.nonpool rr -> W_div.nonpool rx -> W_div.nonpool ry ->
  implM usegs (interp (embed (BN_mul (tree_ops bptr) rr rx ry ls))) s
    (bn_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s ls OW LB lo B m AD EA (fun _ _ _ a0' => a0' = wz 1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz W_fuzz.BN_MUL) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Lemma BN_mul_walk_closed : BN_mul_walk_stmt.
Proof.
  exact (W_mul.BN_mul_walk RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof 368 ltac:(lia) ltac:(lia) HxComba8U.comba8_uok).
Qed.

(* [comment removed for export] *)
Lemma fuzz_one_walk_closed : fuzz_one_walk_stmt W_fuzz.FUZZ_STACK.
Proof.
  unfold fuzz_one_walk_stmt. intros until d.
  refine (W_fuzz.fuzz_one_walk RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof
            W_bin2bn.BN_BIN2BN_STACK BN_MUL_STACK_DEBT W_add.BN_ADD_STACK HxuCall.ECE_STACK _ _ _ _
            (W_bin2bn.BN_bin2bn_walk_h RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof)
            BN_mul_walk_closed
            (W_add.BN_add_walk RF_malloc_spec.rmalloc_spec RF_free_spec.rfree_spec_proof)
            W_cmp.BN_cmp_evt
            (@HxuCall.ERR_clear_error_spec CE__ RN__)
            ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s ls OW LB AD EA lo B errv D d).
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - split; vm_compute; discriminate.
Qed.

Theorem rfuzz_bndiv : rfuzz_one_stmt (LM := LM_bndiv) (LSP := LSP_bndiv).
Proof. apply (rfuzz_of_walk W_fuzz.FUZZ_STACK); [vm_compute; discriminate | exact fuzz_one_walk_closed]. Qed.
End WithCeiling0.
