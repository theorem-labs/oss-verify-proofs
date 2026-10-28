(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptExecB LeptSel.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptPixCopyT O23LeptPixCreateT2 O23LeptCloseSpec O23LeptCascW O23LeptTextSelW O23LeptMorphSeqSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptPixHdr V23LeptCmapValid V23LeptPixCopyT V23LeptMbc V23LeptCloseSpec V23LeptMorphSeqSpec V23LeptMorphSeqW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUdd_iface V23LeptUddLib V23LeptUddT V23LeptUddB V23LeptUddW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptUddLib O23LeptUddSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptSelGP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section UddA.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.

Lemma only_of_mseq_live : forall A A' pixd data cd cv', mseq_live A A' pixd data cd cv' -> O23LeptUddLib.only A A' (O23LeptUddLib.pix_l pixd data cd (c_arr cv')).
Proof.
  intros A A' pixd data cd cv' [[Hc H] | [Hc H]] q Hq; apply H; intro E; apply Hq; subst q;
    first [ apply O23LeptUddLib.pix_l_pix | apply O23LeptUddLib.pix_l_data
          | apply O23LeptUddLib.pix_l_cd; exact Hc | apply O23LeptUddLib.pix_l_arr; exact Hc ].
Qed.

Lemma PIXC_of_pix1 : forall C Ar A m pix w h cd data cv, pix1_at C Ar A m pix w h cd data cv -> pix <> data ->
  O23LeptUddLib.PIXC C A m pix w h cd data cv /\ O23LeptUddLib.offs Ar (O23LeptUddLib.pix_l pix data cd (c_arr cv)).
Proof.
  intros C Ar A m pix w h cd data cv (HP & L1 & L2 & L3 & L4 & L5 & L6 & HC) Hne.
  split.
  - unfold O23LeptUddLib.PIXC, O23LeptUddLib.cmx.
    split; [exact HP|]. split; [exact L1|]. split; [exact L3|]. split; [exact L4|]. split; [exact L6|].
    split; [intro E; apply Hne; symmetry; exact E|].
    destruct HC as [HC | (Hn & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13)]; [left; exact HC | right].
    repeat match goal with |- _ /\ _ => split end; first [assumption | congruence].
  - intros q Hq. destruct (O23LeptUddLib.pix_l_in _ _ _ _ _ Hq) as [-> | [-> | [Hn [-> | ->]]]]; [exact L2 | exact L5 | |].
    + destruct HC as [HC | (_ & _ & _ & _ & _ & C5 & _)]; [contradiction | exact C5].
    + destruct HC as [HC | (_ & _ & _ & _ & _ & _ & C6 & _)]; [contradiction | exact C6].
Qed.

Theorem mseq_udd_of : pixMorphCompSequence_contract -> mseq_udd_contract.
Proof.
  intros HM fr cs C A m md regs s pixs w h cm datas cv ret S CK MB HW HZ Hsp Hs16 Hlo Hhi Hra Hret Hgp Ha0 Ha1 Ha2 HP Hhd Hw Hh Lp Ld Hcm kR bR AR HK HB K.
  apply (HM fr cs C A m md regs s pixs w h cm datas cv ret S CK MB HW HZ Hsp Hs16 Hlo Hhi Hra Hret Hgp Ha0 Ha1 Ha2 HP Hhd Hw Hh Lp Ld Hcm kR bR AR HK HB).
  intros fr' cs' A' m' vm' regs' pixd cd data cv' Z' _ W' CS' R10 _ PM P1 Hne ML AR'.
  destruct (PIXC_of_pix1 C A A' m' pixd w h cd data cv' P1 Hne) as [PC OF].
  exact (K fr' cs' A' m' vm' regs' pixd cd data cv' Z' W' CS' R10 PM PC (only_of_mseq_live A A' pixd data cd cv' ML) OF AR').
Qed.

(* [comment removed for export] *)
Theorem pixUpDownDetect_full_W : pixCloseSafeCompBrick_inplace_contract -> pixUpDownDetect_contract UDD_STACK RK_udd RB_udd.
Proof.
  intros Hc. pose proof (mseq_udd_of (pixMorphCompSequence_W Hc)) as HM.
  exact (pixUpDownDetect_W HM).
Qed.

End UddA.
