(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptDefs LeptRoom.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptBase O23LeptCloseSpec O23LeptCloseW O23LeptOc_iface O23LeptOcW O23LeptUdd_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptUddT O23LeptUddB O23LeptUddW O23LeptUddA O23LeptRoomP8.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23LeptP8Closed () := "C59OSSVerify5KrLib3O23=O23LeptCloseWOpixCloseSafeCompBrick_inplace_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptUddAFpixUpDownDetect_full_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23:O23LeptOcWBpixOrientCorrect_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptUddT9UDD_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptUddW6RK_uddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptUddW6RB_uddC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23?O23LeptP8ClosedHpixUpDownDetect_closed_WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptUddW=RK_udd_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptUddW=RB_udd_nonnegC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23LeptUddW:RB_udd_le1C1?~~~~~~~~~~~~~~~".

Section P8Closed.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O23Pins}.

Theorem pixUpDownDetect_closed_W : pixUpDownDetect_contract UDD_STACK RK_udd RB_udd.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptP8Closed ()) ["P8Closed"] "p;5p;6g0000j51Tg001Fj60Tp,2ALR0p,2CLR1p,3ASRR2p,4PINSR3p,3P16R4P0P1P2P3P4D1E0o"). Qed.

Theorem pixOrientCorrect_closed_W : pixOrientCorrect_contract (OC_STACK UDD_STACK) (RK_oc RK_udd) (RB_oc RB_udd).
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptP8Closed ()) ["P8Closed"] "p;<g002Ql<0Tf4f3f2f1f0g003Wg004Ug005Pg006Kg007\g008^g009`M<0p=1p,2ALp,2CLp,3ASRp,4PINSp,3P16D1o"). Qed.

End P8Closed.
