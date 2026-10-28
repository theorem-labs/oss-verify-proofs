(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptDefs LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptCloseSpec V23LeptCloseW V23LeptOc_iface V23LeptOcW V23LeptUdd_iface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUddT V23LeptUddB V23LeptUddW V23LeptUddA.

Section P8Closed.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.

Theorem pixUpDownDetect_closed_W : pixUpDownDetect_contract UDD_STACK RK_udd RB_udd.
Proof. exact (pixUpDownDetect_full_W pixCloseSafeCompBrick_inplace_W). Qed.

Theorem pixOrientCorrect_closed_W : pixOrientCorrect_contract (OC_STACK UDD_STACK) (RK_oc RK_udd) (RB_oc RB_udd).
Proof. exact (pixOrientCorrect_W UDD_STACK RK_udd RB_udd pixUpDownDetect_closed_W RK_udd_nonneg RB_udd_nonneg RB_udd_le1). Qed.

End P8Closed.
