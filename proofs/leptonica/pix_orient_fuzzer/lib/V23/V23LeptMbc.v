(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Mbc.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition MBC (C : lctx) : Prop := rdn SEGS (c_m0 C) (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1).


Lemma W_mbc : forall C A m md, Cok C -> W C A m md -> MBC C -> rdn SEGS m (Z_to_bv 64 0x127ca0) 4 = Some (Z_to_le_bytes 4 1).
Proof.
  intros C A m md CK HW HM. unfold MBC in HM. rewrite <- HM.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro ll_lg ll_ag ll_errno ll_hcell LLU16] in *.
  apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia |].
  intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
  apply (w_frm _ _ _ _ HW).
  - intros [G _]. destruct (pin_grant x G) as [NI _]. apply NI. unfold inZ. cbn [fst snd ll_img LLU16]. lia.
  - intros G. pose proof (pin_glob x G) as I. unfold inZ in I. cbn [fst snd ll_ag LLU16] in I. lia.
  - intros G. pose proof (pin_errno x G) as I. unfold inZ in I. cbn [fst snd ll_errno LLU16] in I. lia.
  - unfold hcell. cbn [ll_hcell LLU16]. lia.
  - unfold scratch. lia.
Qed.

End Mbc.
