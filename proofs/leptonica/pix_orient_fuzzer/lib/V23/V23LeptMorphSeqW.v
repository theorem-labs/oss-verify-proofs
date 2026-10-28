(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL LeptExec LeptExecW LeptExecT LeptExecFP LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptCloseSpec O23LeptMorphSeqA O23LeptMorphSeqB O23LeptMorphSeqSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptMbc V23LeptCloseSpec V23LeptMorphSeqA V23LeptMorphSeqB V23LeptMorphSeqSpec V23LeptMorphSeqH V23LeptMorphSeqT.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MorphSeqW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.

Theorem pixMorphCompSequence_W : pixCloseSafeCompBrick_inplace_contract -> pixMorphCompSequence_contract.
Proof.
  intros HIN. pose proof (csc_contract_of HIN) as HCSC. unfold pixMorphCompSequence_contract.
  intros fr cs C A m md regs s pixs w h cm datas cv ret S CK MB HW FZ H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12
    PIX HD Hw Hh Lpix Ldat CM kR bR RM HkR HbR K.
  pose proof LSTK_val as LV. unfold MSEQ_STACK, CSC_STACK in Hlo.
  pose proof PIX as [P0 [P64 _]].
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lpix ltac:(lia)) as [B1 B2]. rewrite u_Z2bv in B1, B2 by lia.
  assert (EK : (RK_mseq = 7 + RK_mseqt)%Z) by (unfold RK_mseq, RK_mseqt; lia).
  assert (EB : (RB_mseq w h cm = 7 * 2 ^ 17 + RB_mseqt w h cm)%Z) by (unfold RB_mseq, RB_mseqt; lia).
  assert (NK : (0 <= RK_mseqt)%Z) by (vm_compute; discriminate).
  assert (NB : (0 <= RB_mseqt w h cm)%Z).
  { unfold RB_mseqt. pose proof (RB_pixT_nonneg (4 * (wpl_of w 1 * h))). pose proof (RB_cmapT_le cm).
    pose proof (RB_csc_nonneg 8 w h 1). pose proof (RB_csc_nonneg 1 w h 1). lia. }
  replace (0xa663c : word) with (Z_to_bv 64 0xa663c) by (apply bv_eq; reflexivity).
  apply (mseq_head (mkFP fr cs) C A m md regs s pixs S CK HW H2 Hs16 ltac:(unfold MSEQH_WIN; lia) Hhi H4 H10 H11 H12
           ltac:(lia) ltac:(lia) kR bR RM ltac:(lia) ltac:(lia)).
  intros A1 m1 vm1 r1 sa arr s1 s2 HW1 SUB1 PM1 RM1. intros.
  assert (PIX1 : PIXat m1 pixs (hdv w h 1 cm datas)) by exact (exT_pix_livk A m m1 pixs _ PIX (proj2 PM1) Lpix).
  assert (CM1 : cm = 0%Z \/ (CMAPat m1 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\
                               live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct CM as [CM | [CMa [CMb [CMc CMd]]]]; [left; exact CM | right].
    split; [exact (exT_cmap_livk A m m1 cm cv CMa (proj2 PM1) CMc) |]. split; [exact CMb |].
    split; [exact (SUB1 _ _ CMc) | exact (SUB1 _ _ CMd)]. }
  rewrite <- (with_vmmaps_vmmaps vm1 md) in RM1.
  eapply (mseq_tail HCSC (mkFP fr cs) C A A1 m1 (with_vmmaps vm1 md) r1 regs s pixs w h cm datas sa arr s1 s2 cv ret S);
    try eassumption.
  - exact (SUB1 _ _ Lpix).
  - exact (SUB1 _ _ Ldat).
  - unfold RK_mseqt in *; lia.
  - lia.
  - intros fr' cs' A2 m2 vm2 r2 pixd cd data cv' FZ' FS HW2 CSK R10 SUB2 PM2 P1 NE REST RM2.
    rewrite with_vmmaps_twice in HW2 |- *.
    apply (K fr' cs' A2 m2 vm2 r2 pixd cd data cv' FZ' FS HW2 CSK R10 SUB2).
    + exact (POSTM_trans C A s m m1 m2 PM1 PM2).
    + exact (p1_weaken C A A1 A2 m2 pixd w h cd data cv' P1 SUB1).
    + exact NE.
    + unfold mseq_live. exact (p1_rest_nil A A2 pixd data cd cv' REST).
    + replace (kR - RK_mseq)%Z with (kR - 7 - RK_mseqt)%Z by lia.
      replace (bR - RB_mseq w h cm)%Z with (bR - 7 * 2 ^ 17 - RB_mseqt w h cm)%Z by lia. exact RM2.
Qed.

End MorphSeqW.
