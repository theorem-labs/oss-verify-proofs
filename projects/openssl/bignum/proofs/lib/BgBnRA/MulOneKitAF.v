(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnWords BnWordsCorrect BnModel BnTree BnInv BnSpecs BnMInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2 BnArr.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA UnwindA AsStruct.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import BnAKitAF BnCallAF ExpKitAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma data_one_acc : forall Σ OW LB m, AHEAP Σ OW LB m -> acc bgasegs m DATA_ONE 8.
Proof.
  intros Σ OW LB m H.
  apply (af_lib_acc_lit RT AF Σ m (DATA_ONE, 8, 32) DATA_ONE 8 (AH_art _ _ _ _ H)); [vm_compute; reflexivity | cbn; lia | cbn; lia].
Qed.

Lemma one_viewA : forall Σ OW LB m (ls : bstate bptr) PL EA X,
  AHEAP Σ OW LB m -> lib_state ls m OW PL EA -> mem_inv bgasegs m -> ref_at ls OW PL ROne X ->
  X = CONST_ONE /\ getbn ROne ls = bn_const_one
  /\ ro_cells bgasegs m CONST_ONE (bn_cells DATA_ONE (@bn_const_one bptr))
  /\ limbs_at bgasegs m DATA_ONE [1]
  /\ acc bgasegs m CONST_ONE 24 /\ acc bgasegs m DATA_ONE 8
  /\ CONST_ONE mod 8 = 0 /\ DATA_ONE mod 8 = 0 /\ 0 < CONST_ONE /\ 0 < DATA_ONE /\ CONST_ONE + 24 <= 12345344 /\ DATA_ONE + 8 <= 12345344.
Proof.
  intros Σ OW LB m ls PL EA X HEAP LS MI HX.
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS; pose proof PARTS as (WFS & _).
  pose proof (ref_at_fun _ _ _ _ _ _ ND HX (ref_at_one ls OW PL)) as EX.
  split; [exact EX|].
  split; [destruct WFS as (_ & _ & E & _); exact E|].
  split; [exact (const_one_cells_of_heap _ _ _ _ HEAP)|].
  split. { pose proof (data_one_cells m MI) as DO. unfold ro_cells, cells_at in DO. exact (proj2 DO). }
  split; [exact (const_one_acc _ _ _ _ HEAP)|].
  split; [exact (data_one_acc _ _ _ _ HEAP)|].
  unfold CONST_ONE, DATA_ONE. repeat split; try reflexivity; lia.
Qed.

End WithRT.
